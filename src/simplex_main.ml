type expr =
  | Var of int
  | Const of int
  | Mult of expr * expr
  | Add of expr * expr
  | Neg of expr

let rec string_of_expr = function
  | Var v -> "Var(" ^ string_of_int v ^ ")"
  | Const c -> "Const(" ^ string_of_int c ^ ")"
  | Mult (e1, e2) -> "Mult(" ^ string_of_expr e1 ^ ", " ^ string_of_expr e2 ^ ")"
  | Add (e1, e2) -> "Add(" ^ string_of_expr e1 ^ ", " ^ string_of_expr e2 ^ ")"
  | Neg e -> "Neg(" ^ string_of_expr e ^ ")"

let extract_num env sigma t =
  let s = Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma t) in
  let is_digit c = (c >= '0' && c <= '9') || c = '-' in
  let len = String.length s in
  let buf = Buffer.create len in
  String.iter (fun c -> if is_digit c then Buffer.add_char buf c) s;
  int_of_string (Buffer.contents buf)

(* Match constructors by identity, independently of imports and printed names. *)
let refers_to_global env sigma name term =
  EConstr.isRefX env sigma (Nametab.locate (Libnames.qualid_of_string name)) term

let rec parse_expr env sigma t =
  let open EConstr in
  match kind sigma t with
  | App (c, args) ->
      let len = Array.length args in
      let is name = refers_to_global env sigma ("Lib.PolySimp." ^ name) c in
      if is "Add" then Add (parse_expr env sigma args.(len - 2), parse_expr env sigma args.(len - 1))
      else if is "Mult" then Mult (parse_expr env sigma args.(len - 2), parse_expr env sigma args.(len - 1))
      else if is "Const" then Const (extract_num env sigma args.(len - 1))
      else if is "Var" then Var (extract_num env sigma args.(len - 1))
      else if is "Neg" then Neg (parse_expr env sigma args.(len - 1))
      else failwith "Unsupported expression constructor"
  | _ -> failwith "Unsupported AST node"

let rec parse_list env sigma t =
  let open EConstr in
  match kind sigma t with
  | App (c, args) ->
      let len = Array.length args in
      if refers_to_global env sigma "Corelib.Init.Datatypes.nil" c then []
      else if refers_to_global env sigma "Corelib.Init.Datatypes.cons" c then
        parse_expr env sigma args.(len - 2) :: parse_list env sigma args.(len - 1)
      else failwith "Unsupported list constructor"
  | _ -> failwith "Unsupported list representation"

let extract_multipliers result_str =
  let prefix = "Multipliers: [ " in
  let prefix_len = String.length prefix in
  if String.length result_str >= prefix_len && String.sub result_str 0 prefix_len = prefix then
    let nums_str = String.sub result_str prefix_len (String.length result_str - prefix_len) in
    let tokens = String.split_on_char ' ' nums_str in
    List.filter_map (fun s -> 
      let s = String.trim s in 
      if s = "" || s = "]" then None else Some (int_of_string s)
    ) tokens
  else []

let mk_global name =
  match Nametab.locate (Libnames.qualid_of_string name) with
  | Names.GlobRef.ConstructRef c -> EConstr.UnsafeMonomorphic.mkConstruct c
  | Names.GlobRef.ConstRef c -> EConstr.UnsafeMonomorphic.mkConst c
  | Names.GlobRef.IndRef c -> EConstr.UnsafeMonomorphic.mkInd c
  | Names.GlobRef.VarRef c -> EConstr.mkVar c

let mk_construct name = mk_global name
let mk_App name args = EConstr.mkApp (mk_global name, Array.of_list args)

let rec mk_nat n =
  if n <= 0 then mk_construct "O"
  else mk_App "S" [mk_nat (n - 1)]

let rec mk_pos n =
  if n = 1 then mk_construct "xH"
  else if n mod 2 = 0 then mk_App "xO" [mk_pos (n / 2)]
  else mk_App "xI" [mk_pos (n / 2)]

let cert_of_multiplier idx m =
  let gen = mk_App "Lib.Psatz.Cert_isGen" [mk_nat idx] in
  if m = 0 then mk_App "Lib.Psatz.Cert_isMult" [mk_construct "Lib.Psatz.Cert_IsZ0"; gen]
  else mk_App "Lib.Psatz.Cert_isMult" [mk_App "Lib.Psatz.Cert_isZpos" [mk_pos m]; gen]

let rec eval_ast_at_zero = function
  | Var _ -> 0
  | Const c -> c
  | Mult (e1, e2) -> eval_ast_at_zero e1 * eval_ast_at_zero e2
  | Add (e1, e2) -> eval_ast_at_zero e1 + eval_ast_at_zero e2
  | Neg e -> - (eval_ast_at_zero e)

let get_k multipliers ast_list =
  let sum = List.fold_left2 (fun acc m ast -> acc + m * eval_ast_at_zero ast) 0 multipliers ast_list in
  -sum

let build_certificate multipliers ast_list =
  let base_cert =
    match multipliers with
    | [] -> failwith "No multipliers"
    | [m] -> cert_of_multiplier 0 m
    | m :: ms ->
        let rec aux idx lst =
          match lst with
          | [] -> failwith "impossible"
          | [last_m] -> cert_of_multiplier idx last_m
          | next_m :: rest ->
              mk_App "Lib.Psatz.Cert_isAdd" [cert_of_multiplier idx next_m; aux (idx + 1) rest]
        in
        mk_App "Lib.Psatz.Cert_isAdd" [cert_of_multiplier 0 m; aux 1 ms]
  in
  let k = get_k multipliers ast_list in
  if k = 1 then base_cert
  else if k > 1 then mk_App "Lib.Psatz.Cert_isAdd" [base_cert; mk_App "Lib.Psatz.Cert_isZpos" [mk_pos (k - 1)]]
  else failwith "Math error: K is not positive"

let find_solver () =
  let rec in_checkout dir =
    let path = Filename.concat dir "src/simplex_solver" in
    if Sys.file_exists path then Some path
    else let parent = Filename.dirname dir in
      if parent = dir then None else in_checkout parent
  in
  match in_checkout (Sys.getcwd ()) with
  | Some path -> path
  | None ->
      let path = Filename.concat (Findlib.package_directory "calculus") "simplex_solver" in
      if Sys.file_exists path then path
      else failwith "psatz: cannot find the installed simplex_solver"

let run_dummy_executable expr_list =
  let in_file = Filename.temp_file "rocq_in_" ".txt" in
  let out_file = Filename.temp_file "rocq_out_" ".txt" in
  let oc = open_out in_file in
  List.iter (fun e -> 
    let s = string_of_expr (Neg e) in
    output_string oc (s ^ "\n")
  ) expr_list;
  close_out oc;
  let cmd = Printf.sprintf "%s %s %s"
    (Filename.quote (find_solver ())) (Filename.quote in_file) (Filename.quote out_file) in
  
  let exit_code = Sys.command cmd in
  
  if exit_code <> 0 then failwith (Printf.sprintf "Executable failed with code %d" exit_code);
  let ic = open_in out_file in
  let result = try input_line ic with End_of_file -> "" in
  close_in ic;
  result