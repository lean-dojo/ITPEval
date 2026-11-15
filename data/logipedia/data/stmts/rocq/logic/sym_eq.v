(*
  Statement-only formalization of Logipedia corpus artifact logic.sym_eq
  (catalog title "logic.sym_eq"): equality is symmetric for any two elements
  of any type. This file contains no proof.
*)

Theorem logic_sym_eq :
  forall (A : Type) (x y : A),
    x = y ->
    y = x.
Admitted.
