(* Statement-only formalization of PutnamBench artifact putnam_1976_a4:
   roots of related integer cubics and the coefficient-independent form of
   another root of the irreducible cubic. This file contains no proof. *)

From Stdlib Require Import Reals ZArith QArith.

Open Scope R_scope.

Definition putnam_1976_a4_solution : (R -> R) * (R -> R) :=
  (fun r : R => -1 / (r + 1), fun r : R => -(r + 1) / r).

Definition putnam_1976_a4_P (a b : Z) (x : R) : R :=
  x ^ 3 + IZR a * x ^ 2 + IZR b * x - 1.

Definition putnam_1976_a4_Q (c d : Z) (x : R) : R :=
  x ^ 3 + IZR c * x ^ 2 + IZR d * x + 1.

Definition putnam_1976_a4_irreducible (a b : Z) : Prop :=
  forall q : Q,
    (q ^ 3 + inject_Z a * q ^ 2 + inject_Z b * q - 1)%Q <> 0%Q.

Theorem putnam_1976_a4 :
  forall (a b c d : Z) (r : R),
    putnam_1976_a4_P a b r = 0 ->
    putnam_1976_a4_irreducible a b ->
    putnam_1976_a4_Q c d (r + 1) = 0 ->
    exists s : R,
      putnam_1976_a4_P a b s = 0 /\
      (s = fst putnam_1976_a4_solution r \/
       s = snd putnam_1976_a4_solution r).
Admitted.
