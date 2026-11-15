(*
  Statement-only formalization of Logipedia corpus artifact logic.proj1,
  catalog title "logic.proj1": the first projection of conjunction, stating
  that for arbitrary propositions A and B, A /\ B implies A.
  This file contains no proof.
*)

let statement =
  `!A B:bool. A /\ B ==> A`;;
