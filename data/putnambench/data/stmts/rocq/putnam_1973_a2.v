(* Statement-only formalization of PutnamBench artifact putnam_1973_a2:
   convergence of a periodic signed harmonic series is equivalent to each
   eight-term sign block containing four plus signs. This file contains no proof. *)

From Stdlib Require Import Reals List Arith.

Open Scope R_scope.

Fixpoint putnam_1973_a2_count_ones (L : list R) : nat :=
  match L with
  | nil => O
  | x :: xs =>
      if Req_EM_T x 1
      then S (putnam_1973_a2_count_ones xs)
      else putnam_1973_a2_count_ones xs
  end.

Fixpoint putnam_1973_a2_partial_sum
    (L : list R) (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      putnam_1973_a2_partial_sum L k +
      nth ((S k) mod 8) L 0 / INR (S k)
  end.

Definition putnam_1973_a2_tends_to
    (S : nat -> R) (l : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (S n - l) < epsilon.

Theorem putnam_1973_a2
    (L : list R)
    (hLlength : length L = 8%nat)
    (hLsigns :
      forall i : nat,
        (i < length L)%nat ->
        nth i L 0 = 1 \/ nth i L 0 = -1)
    (pluses : nat)
    (hpluses : pluses = putnam_1973_a2_count_ones L)
    (S : nat -> R)
    (hS : S = putnam_1973_a2_partial_sum L) :
  (exists l : R, putnam_1973_a2_tends_to S l) <->
  pluses = 4%nat.
Admitted.
