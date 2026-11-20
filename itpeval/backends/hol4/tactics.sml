(* This expression runs in the scope of the fixed store_thm proof slot. *)
let
  val output = TextIO.openOut (valOf (OS.Process.getEnv "ITPEVAL_TRACE"))
  fun row fields =
    let fun hex c = StringCvt.padLeft #"0" 2 (Int.fmt StringCvt.HEX (Char.ord c))
    in TextIO.output (output, String.concatWith "\t" (map (String.translate hex) fields) ^ "\n") end
  fun goal tag i (assumptions, conclusion) =
    row (tag :: Int.toString i :: Parse.term_to_string conclusion ::
         map Parse.term_to_string assumptions)
  fun observe i (tac : tactic) g ctxt =
    (goal "enter" i g;
     let val result as (goals, _) = tac g ctxt
     in List.app (goal "subgoal" i) goals; row ["return", Int.toString i]; result end
     handle error => (row ["raise", Int.toString i, General.exnMessage error]; raise error))
  fun finish status = (row [status]; row ["done"]; TextIO.closeOut output)
in
  fn g => fn ctxt =>
    let val result = (ITPEVAL_TACTICS) g ctxt
    in List.app (goal "open" 0) (#1 result); finish "returned"; result end
    handle error => (finish "raised"; raise error)
end
