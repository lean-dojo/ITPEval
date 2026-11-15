(*
  Statement-only formalization of Logipedia corpus artifact logic.proj1
  (catalog title "logic.proj1"): the first projection from a conjunction,
  yielding its left proposition. This file contains no proof.
*)

Theorem logic_proj1 :
  forall A B : Prop,
    A /\ B ->
    A.
Admitted.
