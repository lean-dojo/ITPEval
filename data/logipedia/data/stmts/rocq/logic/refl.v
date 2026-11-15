(*
  Statement-only formalization of Logipedia corpus artifact logic.refl
  (catalog title "logic.refl"): every element of every type is equal to
  itself. This file contains no proof.
*)

Theorem logic_refl :
  forall (A : Type) (x : A),
    x = x.
Admitted.
