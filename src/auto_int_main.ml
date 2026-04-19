
let read_lines file =
  let ic = open_in file in
  let rec read_acc acc =
    try
      let line = input_line ic in
      read_acc (line :: acc)
    with End_of_file ->
      close_in ic;
      List.rev acc
  in
  read_acc []

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

let base_name s =
  let s = if String.length s > 0 && s.[0] = '@' then String.sub s 1 (String.length s - 1) else s in
  try
    let i = String.rindex s '.' in
    String.sub s (i + 1) (String.length s - i - 1)
  with Not_found -> s

let rec extract_num env sigma t =
  let open EConstr in
  match kind sigma t with
  | App (c, [|arg|]) when base_name (Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma c)) = "S" ->
      1 + extract_num env sigma arg
  | Construct _ when base_name (Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma t)) = "O" ->
      0
  | App (c, [|arg|]) when base_name (Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma c)) = "IZR" ->
      extract_num env sigma arg
  | App (c, [|arg|]) when base_name (Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma c)) = "Zpos" ->
      extract_num env sigma arg
  | App (c, [|arg|]) when base_name (Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma c)) = "Zneg" ->
      - extract_num env sigma arg
  | Construct _ when base_name (Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma t)) = "Z0" ->
      0
  | _ ->
      let s = Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma t) in
      let is_digit c = (c >= '0' && c <= '9') || c = '-' in
      let buf = Buffer.create (String.length s) in
      String.iter (fun c -> if is_digit c then Buffer.add_char buf c) s;
      let res = Buffer.contents buf in
      if res = "" then 0 else int_of_string res

let rec parse_prefix lines =
  match !lines with
  | [] -> failwith "Unexpected end of output"
  | token :: rest ->
      lines := rest;
      match token with
      | "EVar" -> mk_construct "EVar"
      | "EConst" ->
          let v = List.hd !lines in
          lines := List.tl !lines;
          let n = try int_of_string v with _ -> int_of_float (float_of_string v) in
          let z = if n >= 0 then 
                    if n = 0 then mk_construct "Z0"
                    else mk_App "Zpos" [mk_pos n]
                  else mk_App "Zneg" [mk_pos (-n)] in
          let r = mk_App "IZR" [z] in
          mk_App "EConst" [r]
      | "ENeg" -> mk_App "ENeg" [parse_prefix lines]
      | "EAdd" -> 
          let e1 = parse_prefix lines in
          let e2 = parse_prefix lines in
          mk_App "EAdd" [e1; e2]
      | "ESub" -> 
          let e1 = parse_prefix lines in
          let e2 = parse_prefix lines in
          mk_App "ESub" [e1; e2]
      | "EMul" -> 
          let e1 = parse_prefix lines in
          let e2 = parse_prefix lines in
          mk_App "EMul" [e1; e2]
      | "EDiv" -> 
          let e1 = parse_prefix lines in
          let e2 = parse_prefix lines in
          mk_App "EDiv" [e1; e2]
      | "ESin" -> mk_App "ESin" [parse_prefix lines]
      | "ECos" -> mk_App "ECos" [parse_prefix lines]
      | "ETan" -> mk_App "ETan" [parse_prefix lines]
      | "ECot" -> mk_App "ECot" [parse_prefix lines]
      | "ESec" -> mk_App "ESec" [parse_prefix lines]
      | "ECsc" -> mk_App "ECsc" [parse_prefix lines]
      | "EExp" -> mk_App "EExp" [parse_prefix lines]
      | "ELog" -> mk_App "ELog" [parse_prefix lines]
      | "ESqrt" -> mk_App "ESqrt" [parse_prefix lines]
      | "ESinh" -> mk_App "ESinh" [parse_prefix lines]
      | "ECosh" -> mk_App "ECosh" [parse_prefix lines]
      | "ETanh" -> mk_App "ETanh" [parse_prefix lines]
      | "EArcsin" -> mk_App "EArcsin" [parse_prefix lines]
      | "EArccos" -> mk_App "EArccos" [parse_prefix lines]
      | "EArctan" -> mk_App "EArctan" [parse_prefix lines]
      | "EPow" ->
          let base = parse_prefix lines in
          let n_str = List.hd !lines in
          lines := List.tl !lines;
          let n = int_of_string n_str in
          mk_App "EPow" [base; mk_nat n]
      | "ERpow" ->
          let base = parse_prefix lines in
          let r_str = List.hd !lines in
          lines := List.tl !lines;
          (try
            let p_str, q_str = match String.split_on_char '/' r_str with | [p;q] -> p,q | _ -> failwith "" in
            let p = int_of_string p_str in
            let q = int_of_string q_str in
            let zp = if p >= 0 then if p = 0 then mk_construct "Z0" else mk_App "Zpos" [mk_pos p] else mk_App "Zneg" [mk_pos (-p)] in
            let zq = if q >= 0 then if q = 0 then mk_construct "Z0" else mk_App "Zpos" [mk_pos q] else mk_App "Zneg" [mk_pos (-q)] in
            let rp = mk_App "IZR" [zp] in
            let rq = mk_App "IZR" [zq] in
            let r = mk_App "Rdiv" [rp; rq] in
            mk_App "ERpow" [base; r]
           with _ ->
            let n = int_of_string r_str in
            let z = if n >= 0 then if n = 0 then mk_construct "Z0" else mk_App "Zpos" [mk_pos n] else mk_App "Zneg" [mk_pos (-n)] in
            let r = mk_App "IZR" [z] in
            mk_App "ERpow" [base; r])
      | "ERpower" -> 
          let e1 = parse_prefix lines in
          let e2 = parse_prefix lines in
          mk_App "ERpower" [e1; e2]
      | _ -> failwith ("Unknown AST token: " ^ token)

let rec convert_coq_expr_to_python_string env sigma t =
  let open EConstr in
  match kind sigma t with
  | App (c, args) ->
      let c_str = base_name (Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma c)) in
      let len = Array.length args in
      (match c_str with
       | "EAdd" -> "(" ^ convert_coq_expr_to_python_string env sigma args.(len - 2) ^ " + " ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "ESub" -> "(" ^ convert_coq_expr_to_python_string env sigma args.(len - 2) ^ " - " ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "EMul" -> "(" ^ convert_coq_expr_to_python_string env sigma args.(len - 2) ^ " * " ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "EDiv" -> "(" ^ convert_coq_expr_to_python_string env sigma args.(len - 2) ^ " / " ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "ENeg" -> "(- " ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "ESin" -> "sin(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "ECos" -> "cos(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "ETan" -> "tan(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "ECot" -> "cot(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "ESec" -> "sec(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "ECsc" -> "csc(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "EExp" -> "exp(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "ELog" -> "log(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "ESqrt" -> "sqrt(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "ESinh" -> "sinh(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "ECosh" -> "cosh(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "ETanh" -> "tanh(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "EArcsin" -> "asin(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "EArccos" -> "acos(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "EArctan" -> "atan(" ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "EPow" -> "(" ^ convert_coq_expr_to_python_string env sigma args.(len - 2) ^ " ** " ^ string_of_int (extract_num env sigma args.(len - 1)) ^ ")"
       | "ERpow" | "ERpower" -> "(" ^ convert_coq_expr_to_python_string env sigma args.(len - 2) ^ " ** " ^ convert_coq_expr_to_python_string env sigma args.(len - 1) ^ ")"
       | "EConst" -> string_of_int (extract_num env sigma args.(len - 1))
       | _ -> failwith ("Unknown App: " ^ c_str))
  | Construct _ ->
      let c_str = base_name (Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma t)) in
      if c_str = "EVar" then "x" else failwith ("Unknown Construct: " ^ c_str)
  | _ -> 
      let s = base_name (Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma t)) in
      if s = "EVar" then "x" else failwith ("Unsupported expr node: " ^ s)

let find_script () =
  let cwd = Sys.getcwd () in
  let candidates = [
    Filename.concat cwd "src/auto_int.py";
    Filename.concat cwd "../src/auto_int.py";
    Filename.concat cwd "../../src/auto_int.py";
    "/home/sij/Calculus-with-Coq/src/auto_int.py"
  ] in
  try List.find Sys.file_exists candidates
  with Not_found -> failwith "Could not find auto_int.py script. Please ensure you are in the project directory."

let run_auto_int env sigma f_term =
  let expr_str = convert_coq_expr_to_python_string env sigma f_term in
  let in_file = Filename.temp_file "auto_int_in_" ".txt" in
  let out_file = Filename.temp_file "auto_int_out_" ".txt" in
  
  let oc = open_out in_file in
  output_string oc expr_str;
  close_out oc;
  
  let python_exe = "python3" in
  let script_path = find_script () in
  let cmd = Printf.sprintf "%s %s %s %s" python_exe script_path in_file out_file in
  let exit_code = Sys.command cmd in
  if exit_code <> 0 then failwith (Printf.sprintf "auto_int script failed with code %d. Command was: %s" exit_code cmd);
  
  let lines = ref (read_lines out_file) in
  parse_prefix lines

