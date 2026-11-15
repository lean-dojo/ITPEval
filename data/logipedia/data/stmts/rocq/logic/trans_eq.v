(*
  Statement-only formalization of Logipedia corpus artifact logic.trans_eq
  (catalog title "logic.trans_eq"): equality is transitive for any three
  elements of an arbitrary type. This file contains no proof.
*)

Theorem logic_trans_eq :
  forall (A : Type) (x y z : A),
    x = y ->
    y = z ->
    x = z.
Admitted.
