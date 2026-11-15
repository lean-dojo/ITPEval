(* Statement-only formalization of PutnamBench artifact putnam_1971_b3:
   the Lebesgue measure of the times when one integer lap count is twice the
   delayed lap count is one, for every positive delay. This file contains no
   proof. *)

From Stdlib Require Import Reals ZArith.

Open Scope R_scope.

Definition real_set := R -> Prop.

Record open_interval : Type := {
  interval_lower : R;
  interval_upper : R
}.

Definition in_open_interval
    (interval : open_interval) (x : R) : Prop :=
  interval_lower interval < x < interval_upper interval.

Definition interval_length (interval : open_interval) : R :=
  Rmax 0 (interval_upper interval - interval_lower interval).

Definition intervals_cover
    (A : real_set) (intervals : nat -> open_interval) : Prop :=
  forall x : R,
    A x ->
    exists n : nat, in_open_interval (intervals n) x.

Fixpoint partial_interval_length
    (intervals : nat -> open_interval) (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      partial_interval_length intervals k +
      interval_length (intervals k)
  end.

(* This is the countable-open-interval characterization of one-dimensional
   Lebesgue outer measure. *)
Definition has_lebesgue_measure
    (A : real_set) (measure : R) : Prop :=
  0 <= measure /\
  (forall intervals : nat -> open_interval,
    intervals_cover A intervals ->
    forall lower : R,
      lower < measure ->
      exists n : nat,
        lower < partial_interval_length intervals n) /\
  (forall epsilon : R,
    0 < epsilon ->
    exists intervals : nat -> open_interval,
      intervals_cover A intervals /\
      forall n : nat,
        partial_interval_length intervals n < measure + epsilon).

Definition putnam_1971_b3_times (T : R) : real_set :=
  fun t : R =>
    T <= t /\
    Int_part t = (2 * Int_part (t - T))%Z.

Theorem putnam_1971_b3
    (T : R)
    (hT : 0 < T) :
  has_lebesgue_measure (putnam_1971_b3_times T) 1.
Admitted.
