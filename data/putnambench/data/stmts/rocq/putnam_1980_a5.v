From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals trigo lebesgue_integral lebesgue_measure measure.
From mathcomp Require Import classical_sets cardinality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Variable R : realType.
Definition mu := [the measure _ _ of @lebesgue_measure R].
Definition putnam_1980_a5_interval_integral (f : R -> R) (a b : R) : R :=
  if a <= b then
    \int[mu]_(t in [set t : R | a <= t <= b]) f t
  else
    - \int[mu]_(t in [set t : R | b <= t <= a]) f t.

Theorem putnam_1980_a5
    (P : {poly R})
    (Pnonconst : gtn (size P) (1%nat))
    : finite_set [set x : R |
        putnam_1980_a5_interval_integral (fun t => P.[t] * sin t) 0 x = 0 /\
        putnam_1980_a5_interval_integral (fun t => P.[t] * cos t) 0 x = 0].
Proof. Admitted.
