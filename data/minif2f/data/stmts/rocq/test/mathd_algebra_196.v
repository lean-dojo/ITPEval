Require Import Reals.
Require Import List.

Open Scope R_scope.

(*
  Statement-only formalization of miniF2F test problem mathd_algebra_196:
  the sum of the finite solution set of |2 - x| = 3 is 4.
*)

Theorem mathd_algebra_196 :
  forall S : list R,
  NoDup S ->
  (forall x : R, In x S <-> Rabs (2 - x) = 3) ->
  fold_right Rplus 0 S = 4.

Proof.
