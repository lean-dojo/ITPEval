From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals exp sequences topology normedtype measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Variable R : realType.
Definition mu := [the measure _ _ of @lebesgue_measure R].
Theorem putnam_1968_b4
    (f : R -> R)
    (hf : continuous f /\ (exists r : R,
        (fun y : R => \int[mu]_(x in [set x : R | -y <= x <= y]) f x) @ +oo --> r))
    : exists r : R, 
        (fun y : R => \int[mu]_(x in [set x : R |
            (-y <= x <= -(1 / y)) \/ (1 / y <= x <= y)]) f (x - 1 / x)) @ +oo --> r /\
        (fun y : R => \int[mu]_(x in [set x : R | -y <= x <= y]) f x) @ +oo --> r.
Proof. Admitted.
