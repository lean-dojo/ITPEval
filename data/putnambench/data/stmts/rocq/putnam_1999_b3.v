(* Statement-only formalization of PutnamBench corpus artifact putnam_1999_b3:
   evaluation of a restricted two-variable limit involving a doubly infinite
   power series over positive integer pairs; this file contains no proof. *)

From Stdlib Require Import Reals SeqSeries ClassicalEpsilon.

Open Scope R_scope.

Definition putnam_1999_b3_solution : R := 3.

Definition putnam_1999_b3_term
    (x y : R) (m n : nat) : R :=
  if Nat.eq_dec m O then 0
  else if Nat.eq_dec n O then 0
  else if Rle_dec (1 / 2) (INR m / INR n) then
    if Rle_dec (INR m / INR n) 2 then
      x ^ m * y ^ n
    else 0
  else 0.

Definition putnam_1999_b3_series_value (f : nat -> R) : R :=
  epsilon (inhabits (0 : R))
    (fun value : R => infinite_sum f value).

Definition putnam_1999_b3_series (x y : R) : R :=
  putnam_1999_b3_series_value
    (fun m : nat =>
      putnam_1999_b3_series_value
        (fun n : nat => putnam_1999_b3_term x y m n)).

Definition putnam_1999_b3_restricted_limit
    (A : (R * R)%type -> Prop)
    (f : (R * R)%type -> R)
    (l : R) : Prop :=
  forall eps : R,
    0 < eps ->
    exists delta : R,
      0 < delta /\
      forall xy : (R * R)%type,
        A xy ->
        sqrt ((fst xy - 1) ^ 2 + (snd xy - 1) ^ 2) < delta ->
        Rabs (f xy - l) < eps.

Theorem putnam_1999_b3
    (A : (R * R)%type -> Prop)
    (S : R -> R -> R)
    (hA : A =
      fun xy : (R * R)%type =>
        0 <= fst xy /\ fst xy < 1 /\
        0 <= snd xy /\ snd xy < 1)
    (hS : S = putnam_1999_b3_series) :
  putnam_1999_b3_restricted_limit A
    (fun xy : (R * R)%type =>
      (1 - fst xy * (snd xy) ^ 2) *
      (1 - (fst xy) ^ 2 * snd xy) *
      S (fst xy) (snd xy))
    putnam_1999_b3_solution.
Admitted.
