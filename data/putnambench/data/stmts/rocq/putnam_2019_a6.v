From mathcomp Require Import all_ssreflect ssrnum ssralg.
From mathcomp Require Import reals derive normedtype sequences topology exp.
From mathcomp Require Import classical_sets.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Variable R : realType.
Definition at_right := fun (x : R) => within (fun y => y > x) (nbhs x).
Theorem putnam_2019_a6
    (g : R -> R)
    (r : R)
    (hcont : {within [set x | 0 <= x <= 1], continuous g})
    (hdiff : forall x : R,
      0 < x < 1 -> differentiable g x /\ differentiable g^`() x)
    (hr : r > 1)
    (hlim : (fun x : R => g x / (expR (r * ln x))) @ (at_right 0) --> 0)
    : g^`() @ (at_right 0) --> 0 \/
      forall M delta : R,
        0 < delta ->
        exists x' : R,
          0 < x' /\
          x' < delta /\
          x' < 1 /\
          M < expR (r * ln x') * `|g^`(2) x'|.
Proof. Admitted.
