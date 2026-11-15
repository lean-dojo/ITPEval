(* Statement-only formalization of PutnamBench corpus artifact putnam_2024_b3
   (putnambench__rocq__putnam_2024_b3): bounds on consecutive positive
   solutions of tan x = x and their excess spacing over pi. This file
   contains no proof. *)

From Stdlib Require Import Reals Arith.PeanoNat.

Open Scope R_scope.

Definition putnam_2024_b3_strictly_increasing
    (r : nat -> R) : Prop :=
  forall m n : nat,
    (1 <= m)%nat ->
    (m < n)%nat ->
    r m < r n.

Definition putnam_2024_b3_enumerates_positive_roots
    (r : nat -> R) : Prop :=
  putnam_2024_b3_strictly_increasing r /\
  (forall x : R,
      0 < x < r 1%nat ->
      tan x <> x) /\
  forall n : nat,
    (1 <= n)%nat ->
    0 < r n /\
    tan (r n) = r n /\
    forall x : R,
      r n < x < r (S n) ->
      tan x <> x.

Theorem putnam_2024_b3 :
  forall (r : nat -> R) (n : nat),
    putnam_2024_b3_enumerates_positive_roots r ->
    (1 <= n)%nat ->
    0 < r (S n) - r n - PI /\
    r (S n) - r n - PI <
      1 / (INR ((n ^ 2 + n)%nat) * PI).
Admitted.
