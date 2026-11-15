(*
  Statement-only formalization of Logipedia corpus artifact logic.proj2
  (catalog title "logic.proj2"): the second projection from a conjunction,
  yielding its right proposition. This file contains no proof.
*)

Theorem logic_proj2 :
  forall A B : Prop,
    A /\ B ->
    B.
Admitted.
