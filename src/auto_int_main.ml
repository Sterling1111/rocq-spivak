
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
  if Z.equal n Z.one then mk_construct "xH"
  else if Z.equal (Z.rem n (Z.of_int 2)) Z.zero then
    mk_App "xO" [mk_pos (Z.div n (Z.of_int 2))]
  else mk_App "xI" [mk_pos (Z.div n (Z.of_int 2))]

let mk_real s =
  let n = Z.of_string s in
  let z = if Z.equal n Z.zero then mk_construct "Z0"
    else mk_App (if Z.sign n > 0 then "Zpos" else "Zneg") [mk_pos (Z.abs n)] in
  mk_App "IZR" [z]

(* Inspect kernel names, independent of pretty-printing flags and notations. *)
let node_name env sigma t =
  match EConstr.kind sigma t with
  | Constr.Const (c, _) -> Names.Label.to_string (Names.Constant.label c)
  | Constr.Construct (((mind, i), j), _) ->
      let body = Environ.lookup_mind mind env in
      Names.Id.to_string body.Declarations.mind_packets.(i).Declarations.mind_consnames.(j - 1)
  | _ -> failwith "auto_int: expected a concrete expression or numeric constructor"

let rec extract_integer env sigma t =
  let head, args = match EConstr.kind sigma t with
    | Constr.App (c, args) -> c, args
    | _ -> t, [||] in
  let unary f = if Array.length args <> 1 then failwith "auto_int: malformed integer"
    else f (extract_integer env sigma args.(0)) in
  match node_name env sigma head with
  | "O" | "Z0" -> Z.zero
  | "xH" -> Z.one
  | "S" -> unary Z.succ
  | "IZR" | "Zpos" -> unary (fun n -> n)
  | "Zneg" -> unary Z.neg
  | "xO" -> unary (fun n -> Z.mul (Z.of_int 2) n)
  | "xI" -> unary (fun n -> Z.succ (Z.mul (Z.of_int 2) n))
  | name -> failwith ("auto_int: unsupported integer: " ^ name)

let take lines = match !lines with
  | [] -> failwith "auto_int: truncated primitive"
  | x :: xs -> lines := xs; x

let rec parse_prefix lines =
  match !lines with
  | [] -> failwith "Unexpected end of output"
  | token :: rest ->
      lines := rest;
      match token with
      | "EVar" -> mk_construct "EVar"
      | "EConst" ->
          mk_App "EConst" [mk_real (take lines)]
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
          let n = int_of_string (take lines) in
          if n < 0 then failwith "auto_int: negative natural exponent";
          mk_App "EPow" [base; mk_nat n]
      | "ERpow" ->
          let base = parse_prefix lines in
          let r = match String.split_on_char '/' (take lines) with
            | [p; q] -> mk_App "Rdiv" [mk_real p; mk_real q]
            | [n] -> mk_real n
            | _ -> failwith "auto_int: malformed rational exponent" in
          mk_App "ERpow" [base; r]
      | "ERpower" -> 
          let e1 = parse_prefix lines in
          let e2 = parse_prefix lines in
          mk_App "ERpower" [e1; e2]
      | _ -> failwith ("Unknown AST token: " ^ token)

let convert_coq_expr_to_python_string env sigma t =
  let buf = Buffer.create 128 in
  let add = Buffer.add_string buf in
  let rec emit t =
    let head, args = match EConstr.kind sigma t with
      | Constr.App (c, args) -> c, args
      | _ -> t, [||] in
    let unary name = add name; add "("; emit args.(0); add ")" in
    let binary op = add "("; emit args.(0); add op; emit args.(1); add ")" in
    match node_name env sigma head with
    | "EVar" -> add "x"
    | "EConst" -> emit args.(0)
    | "IZR" | "INR" -> add (Z.to_string (extract_integer env sigma args.(0)))
    | "EAdd" | "Rplus" -> binary " + "
    | "ESub" | "Rminus" -> binary " - "
    | "EMul" | "Rmult" -> binary " * "
    | "EDiv" | "Rdiv" -> binary " / "
    | "ENeg" | "Ropp" -> unary "-"
    | "Rinv" -> add "(1 / "; emit args.(0); add ")"
    | "ESin" | "sin" -> unary "sin"
    | "ECos" | "cos" -> unary "cos"
    | "ETan" | "tan" -> unary "tan"
    | "ECot" | "cot" -> unary "cot"
    | "ESec" | "sec" -> unary "sec"
    | "ECsc" | "csc" -> unary "csc"
    | "EExp" | "exp" -> unary "exp"
    | "ELog" | "log" | "ln" -> unary "log"
    | "ESqrt" | "sqrt" -> unary "sqrt"
    | "ESinh" | "sinh" -> unary "sinh"
    | "ECosh" | "cosh" -> unary "cosh"
    | "ETanh" | "tanh" -> unary "tanh"
    | "EArcsin" | "arcsin" -> unary "asin"
    | "EArccos" | "arccos" -> unary "acos"
    | "EArctan" | "arctan" -> unary "atan"
    | "EPow" | "pow" ->
        add "("; emit args.(0); add " ** ";
        add (Z.to_string (extract_integer env sigma args.(1))); add ")"
    | "ERpow" | "ERpower" | "Rpower" -> binary " ** "
    | name -> failwith ("auto_int: unsupported expression: " ^ name)
  in
  emit t; Buffer.contents buf

let find_script () =
  match Sys.getenv_opt "AUTO_INT_SCRIPT" with
  | Some path -> path
  | None ->
      let rec search dir =
        let path = Filename.concat dir "src/auto_int.py" in
        if Sys.file_exists path then path
        else let parent = Filename.dirname dir in
          if parent = dir then
            failwith "auto_int: cannot find src/auto_int.py; set AUTO_INT_SCRIPT"
          else search parent in
      search (Sys.getcwd ())

(* One untrusted candidate generator per Rocq process. Only text is cached:
   no terms or proofs survive changes to Rocq's environment or undo. *)
type worker = { pid : int; input : Unix.file_descr; output : out_channel;
                script : string; stamp : float; python : string }
let worker = ref None
let cache = Hashtbl.create 127

let stop_worker () =
  match !worker with
  | None -> ()
  | Some w ->
      worker := None;
      close_out_noerr w.output;
      (try Unix.close w.input with Unix.Unix_error _ -> ());
      (try Unix.kill w.pid Sys.sigkill with Unix.Unix_error _ -> ());
      (try ignore (Unix.waitpid [] w.pid) with Unix.Unix_error _ -> ())

let () = at_exit stop_worker

let get_worker () =
  let script = find_script () in
  let stamp = (Unix.stat script).Unix.st_mtime in
  let python = Stdlib.Option.value (Sys.getenv_opt "AUTO_INT_PYTHON") ~default:"python3" in
  match !worker with
  | Some w when w.script = script && w.stamp = stamp && w.python = python -> w
  | _ ->
      stop_worker (); Hashtbl.clear cache;
      let child_in, parent_out = Unix.pipe ~cloexec:true () in
      let parent_in, child_out = Unix.pipe ~cloexec:true () in
      let pid = try
        Unix.create_process python [|python; "-u"; script; "--server"|]
          child_in child_out Unix.stderr
      with exn ->
        List.iter Unix.close [child_in; parent_out; parent_in; child_out]; raise exn in
      Unix.close child_in; Unix.close child_out;
      let w = {pid; input = parent_in;
               output = Unix.out_channel_of_descr parent_out; script; stamp; python} in
      worker := Some w; w

let read_response w =
  let seconds = match Sys.getenv_opt "AUTO_INT_TIMEOUT" with
    | None -> 30.
    | Some s -> (try float_of_string s with Failure _ ->
        failwith "auto_int: AUTO_INT_TIMEOUT must be a positive number") in
  if not (seconds > 0. && seconds < infinity) then
    failwith "auto_int: AUTO_INT_TIMEOUT must be a finite positive number";
  let deadline = Unix.gettimeofday () +. seconds in
  let response = Buffer.create 256 in
  let chunk = Bytes.create 4096 in
  let rec wait () =
    Control.check_for_interrupt ();
    if Unix.gettimeofday () >= deadline then
      failwith "auto_int: SymPy timed out (configure AUTO_INT_TIMEOUT in seconds)";
    let ready, _, _ = Unix.select [w.input] [] [] 0.05 in
    if ready = [] then wait () else
      let n = Unix.read w.input chunk 0 (Bytes.length chunk) in
      if n = 0 then raise End_of_file;
      Buffer.add_subbytes response chunk 0 n;
      if Buffer.length response > 16 * 1024 * 1024 then
        failwith "auto_int: primitive exceeds 16 MiB";
      (* Read incrementally so a stalled partial response remains interruptible. *)
      match Bytes.index_opt (Bytes.sub chunk 0 n) '\n' with
      | None -> wait ()
      | Some i when i = n - 1 ->
          Buffer.sub response 0 (Buffer.length response - 1)
      | Some _ -> failwith "auto_int: extra worker response" in
  wait ()

let run_auto_int env sigma f_term =
  try
    let expr_str = convert_coq_expr_to_python_string env sigma f_term in
    let w = get_worker () in
    let tokens = match Hashtbl.find_opt cache expr_str with
      | Some tokens -> tokens
      | None ->
          let response = try
            output_string w.output (expr_str ^ "\n"); flush w.output;
            read_response w
          with exn -> stop_worker (); raise exn in
          if Stdlib.String.starts_with ~prefix:"ERROR " response then
            failwith ("auto_int: " ^ String.sub response 6 (String.length response - 6));
          if not (Stdlib.String.starts_with ~prefix:"OK " response) then
            (stop_worker (); failwith "auto_int: malformed worker response");
          let tokens = String.split_on_char ' ' (String.sub response 3 (String.length response - 3)) in
          (* Bound memory in long-running editor sessions. *)
          if Hashtbl.length cache >= 256 then Hashtbl.clear cache;
          Hashtbl.add cache expr_str tokens; tokens in
    let lines = ref tokens in
    let result = parse_prefix lines in
    if !lines <> [] then failwith "auto_int: trailing primitive tokens";
    result
  with
  | Unix.Unix_error (err, fn, _) ->
      stop_worker (); failwith ("auto_int: " ^ fn ^ ": " ^ Unix.error_message err)
  | End_of_file | Sys_error _ ->
      stop_worker (); failwith "auto_int: SymPy worker exited unexpectedly"
