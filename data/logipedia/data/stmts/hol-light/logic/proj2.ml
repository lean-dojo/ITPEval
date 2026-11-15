(*
  Statement-only formalization of Logipedia corpus artifact logic.proj2,
  catalog title "logic.proj2": the second projection of conjunction, stating
  that for arbitrary propositions A and B, A /\ B implies B.
  This file contains no proof.
*)

let statement =
  `!A B:bool. A /\ B ==> B`;;
