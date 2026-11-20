(* This expression runs in the scope of the fixed prove tactic argument. *)
let output = open_out (Sys.getenv "ITPEVAL_TRACE") in
let row fields =
  let hex s = String.concat "" (List.init (String.length s)
    (fun i -> Printf.sprintf "%02x" (Char.code s.[i]))) in
  output_string output (String.concat "\t" (List.map hex fields) ^ "\n") in
let goal tag i (assumptions, conclusion) =
  row (tag :: string_of_int i :: string_of_term conclusion ::
       List.map (fun (_, th) -> string_of_term (concl th)) assumptions) in
let observe i (tac : tactic) g =
  goal "enter" i g;
  try let (_, goals, _) as result = tac g in
      List.iter (goal "subgoal" i) goals; row ["return"; string_of_int i]; result
  with error -> row ["raise"; string_of_int i; Printexc.to_string error]; raise error in
let finish status = row [status]; row ["done"]; close_out output in
fun g -> match (ITPEVAL_TACTICS) g with
         | (_, goals, _) as result ->
             List.iter (goal "open" 0) goals; finish "returned"; result
         | exception error -> finish "raised"; raise error
