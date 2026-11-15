(* Statement-only formalization of PutnamBench artifact putnam_1975_b3:
   the sharp supremum of a normalized elementary symmetric sum over finite
   families of positive real numbers. This file contains no proof. *)

From Stdlib Require Import Reals List Arith.Factorial.

Open Scope R_scope.

Fixpoint putnam_1975_b3_esymm
    (k : nat) (a : list R) {struct a} : R :=
  match a, k with
  | _, O => 1
  | nil, S _ => 0
  | x :: xs, S j =>
      putnam_1975_b3_esymm (S j) xs +
      x * putnam_1975_b3_esymm j xs
  end.

Definition putnam_1975_b3_ratio
    (k : nat) (a : list R) : R :=
  putnam_1975_b3_esymm k a /
  (putnam_1975_b3_esymm 1 a) ^ k.

Definition putnam_1975_b3_solution (k : nat) : R :=
  1 / INR (fact k).

Theorem putnam_1975_b3 :
  forall k : nat,
    (0 < k)%nat ->
    (forall a : list R,
      Forall (fun x : R => 0 < x) a ->
      (k <= length a)%nat ->
      putnam_1975_b3_ratio k a <= putnam_1975_b3_solution k) /\
    forall M : R,
      M < putnam_1975_b3_solution k ->
      exists a : list R,
        Forall (fun x : R => 0 < x) a /\
        (k <= length a)%nat /\
        M < putnam_1975_b3_ratio k a.
Admitted.
