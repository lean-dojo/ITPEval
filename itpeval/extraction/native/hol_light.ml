(* The compiler's type path distinguishes a kernel thm value from an arbitrary
   OCaml value. Source locations are those of the binding in the compiler env. *)
let itp_root = Sys.getenv "ITPEVAL_PROJECT";;
let itp_output = open_out (Sys.getenv "ITPEVAL_OUTPUT");;
let itp_row fields =
  let hex s = String.concat "" (List.init (String.length s)
    (fun i -> Printf.sprintf "%02x" (Char.code s.[i]))) in
  output_string itp_output (String.concat "\t" (List.map hex fields) ^ "\n");;
let itp_relative file =
  let path = if Filename.is_relative file then Filename.concat (Sys.getcwd ()) file else file in
  let prefix = itp_root ^ "/" in
  if String.starts_with ~prefix path then
    Some (String.sub path (String.length prefix) (String.length path - String.length prefix))
  else None;;
(* Capture the registration at the HOL definition API, whose returned theorem
   can have quantified arguments missing from the primitive defining axiom. *)
let itp_defined = ref ([] : (string * thm) list);;
let itp_record_definition f tm =
  let th = f tm in
  let _,body = strip_forall (concl th) in
  let constant,_ = strip_comb (lhs body) in
  itp_defined := (fst (dest_const constant),th) :: !itp_defined; th;;
let new_definition = itp_record_definition new_definition;;
let new_basic_definition = itp_record_definition new_basic_definition;;
let itp_type_path vd =
  match Types.get_desc vd.Types.val_type with
  | Types.Tconstr(p,[],_) -> Some p
  | _ -> None;;
let itp_kernel_type =
  let _,vd = Env.find_value_by_name (Longident.Lident "TRUTH") !Toploop.toplevel_env in
  match itp_type_path vd with Some p -> p | None -> failwith "TRUTH has no theorem type";;
let itp_bindings = Hashtbl.create 31;;
let itp_binding name path vd rows =
  let loc = vd.Types.val_loc in
  match itp_type_path vd with
  | Some p when Path.same p itp_kernel_type && Sys.file_exists loc.Location.loc_start.Lexing.pos_fname ->
      (match itp_relative loc.Location.loc_start.Lexing.pos_fname with
       | Some file ->
           let key = file,name,loc.Location.loc_start.Lexing.pos_cnum in
           if Hashtbl.mem itp_bindings key then rows else
           let th : thm = Obj.obj (Toploop.eval_value_path !Toploop.toplevel_env path) in
           let kind = if List.mem th (axioms()) then "axiom"
                      else if List.exists (fun (_,v) -> v == th) !itp_defined ||
                              List.mem th (definitions()) then "definition" else "theorem" in
           Hashtbl.add itp_bindings key ();
           (loc.Location.loc_start.Lexing.pos_cnum, ["decl";file;name;kind;string_of_term (concl th);
             string_of_int loc.Location.loc_start.Lexing.pos_cnum;
             string_of_int loc.Location.loc_end.Lexing.pos_cnum;
             (try fst (List.find (fun (_,v) -> v == th) !itp_defined) with Not_found -> "")] @
             List.map string_of_term (hyp th)) :: rows
       | None -> rows)
  | _ -> rows;;

let itp_capture () =
  let rows = Env.fold_values itp_binding None !Toploop.toplevel_env [] in
  List.iter (fun (_,r) -> itp_row r) (List.sort compare rows);;
let itp_capture_loader = !file_loader;;
let itp_stack = ref [];;
file_loader := (fun file ->
  match itp_relative file with
  | None -> itp_capture_loader file
  | Some path ->
      itp_capture ();
      let before = !itp_stack in
      itp_row ["source";path];
      (match before with parent::_ -> itp_row ["import";parent;path] | [] -> ());
      itp_stack := path::before;
      Fun.protect ~finally:(fun () -> itp_stack := before) (fun () ->
        let result = itp_capture_loader file in
        itp_capture (); result));;
Sys.chdir itp_root;;
load_path := itp_root :: !load_path;;
loadt (Sys.getenv "ITPEVAL_ENTRY");;
file_loader := itp_capture_loader;;
itp_row ["done"]; close_out itp_output;;
