(*
  Statement-only formalization of Logipedia corpus artifact logic.not_to_not,
  catalog title "logic.not_to_not": contraposition for arbitrary propositions,
  from A implying B and not B, infer not A. This file contains no proof.
*)

let logic_not_to_not =
  `!A B:bool. (A ==> B) ==> ~B ==> ~A`;;
