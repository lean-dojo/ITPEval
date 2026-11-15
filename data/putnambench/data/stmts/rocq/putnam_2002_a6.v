(* Statement-only formalization of PutnamBench corpus artifact putnam_2002_a6:
   convergence of a recursively defined reciprocal series according to the
   base-b digit length, with exactly base 2 qualifying; this file contains no
   proof. *)

From Stdlib Require Import Reals Arith.PeanoNat SeqSeries.

Open Scope R_scope.

Fixpoint putnam_2002_a6_digit_length_fuel
    (fuel b n : nat) : nat :=
  match fuel with
  | O => O
  | S fuel' =>
      if Nat.ltb n b
      then 1%nat
      else S (putnam_2002_a6_digit_length_fuel
                fuel' b (Nat.div n b))
  end.

Definition putnam_2002_a6_digit_length
    (b n : nat) : nat :=
  if Nat.ltb b 2
  then O
  else putnam_2002_a6_digit_length_fuel (S n) b n.

Fixpoint putnam_2002_a6_partial_sum
    (f : nat -> nat -> R) (b m : nat) : R :=
  match m with
  | O => 0
  | S m' =>
      putnam_2002_a6_partial_sum f b m' + 1 / f b (S m')
  end.

Definition putnam_2002_a6_converges
    (f : nat -> nat -> R) (b : nat) : Prop :=
  exists limit : R,
    Un_cv (fun m : nat => putnam_2002_a6_partial_sum f b m) limit.

Definition putnam_2002_a6_solution (b : nat) : Prop :=
  b = 2%nat.

Theorem putnam_2002_a6 :
  forall f : nat -> nat -> R,
    (forall b : nat,
      f b 1%nat = 1 /\
      f b 2%nat = 2 /\
      forall n : nat,
        (3 <= n)%nat ->
        f b n =
          INR n * f b (putnam_2002_a6_digit_length b n)) ->
    forall b : nat,
      (2 <= b)%nat ->
      (putnam_2002_a6_converges f b <->
       putnam_2002_a6_solution b).
Admitted.
