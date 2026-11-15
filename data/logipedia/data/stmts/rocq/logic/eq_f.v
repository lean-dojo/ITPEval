(*
  Statement-only formalization of Logipedia corpus artifact logic.eq_f
  (catalog title "logic.eq_f"): every function preserves equality of its
  inputs. This file contains no proof.
*)

Theorem logic_eq_f :
  forall (A B : Type) (f : A -> B) (x y : A),
    x = y ->
    f x = f y.
Admitted.
