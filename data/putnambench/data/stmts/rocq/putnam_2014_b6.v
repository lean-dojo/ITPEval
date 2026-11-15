(* Statement-only formalization of PutnamBench corpus artifact putnam_2014_b6:
   a Lipschitz real function with integer-affine values at rational points of
   the unit interval is affine on each interval of a finite closed-interval
   cover. This file contains no proof. *)

From Stdlib Require Import Reals ZArith QArith Lists.List.

Open Scope R_scope.

Definition putnam_2014_b6_in_unit_interval (x : R) : Prop :=
  0 <= x <= 1.

Definition putnam_2014_b6_lipschitz_on_unit_interval
    (f : R -> R) : Prop :=
  exists K : R,
    0 < K /\
    forall x y : R,
      putnam_2014_b6_in_unit_interval x ->
      putnam_2014_b6_in_unit_interval y ->
      Rabs (f x - f y) <= K * Rabs (x - y).

Definition putnam_2014_b6_integer_affine_at_rationals
    (f : R -> R) : Prop :=
  forall r : Q,
    (0 <= r <= 1)%Q ->
    exists a b : Z,
      f (Q2R r) = IZR a + IZR b * Q2R r.

Definition putnam_2014_b6_in_closed_interval
    (interval : (R * R)%type) (x : R) : Prop :=
  fst interval <= x <= snd interval.

Definition putnam_2014_b6_affine_on
    (f : R -> R) (interval : (R * R)%type) : Prop :=
  exists m c : R,
    forall x : R,
      putnam_2014_b6_in_closed_interval interval x ->
      f x = c + m * x.

Definition putnam_2014_b6_covered_by
    (intervals : list (R * R)%type) (x : R) : Prop :=
  exists interval : (R * R)%type,
    List.In interval intervals /\
    putnam_2014_b6_in_closed_interval interval x.

Theorem putnam_2014_b6
    (f : R -> R)
    (hlip : putnam_2014_b6_lipschitz_on_unit_interval f)
    (hrat : putnam_2014_b6_integer_affine_at_rationals f) :
  exists intervals : list (R * R)%type,
    (forall interval : (R * R)%type,
      List.In interval intervals ->
      fst interval <= snd interval /\
      putnam_2014_b6_affine_on f interval) /\
    forall x : R,
      putnam_2014_b6_in_unit_interval x <->
      putnam_2014_b6_covered_by intervals x.
Admitted.
