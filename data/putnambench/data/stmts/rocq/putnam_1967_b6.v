From mathcomp Require Import all_ssreflect ssrnum ssralg.
From mathcomp Require Import reals normedtype derive topology sequences.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Variable R : realType.
Theorem putnam_1967_b6
    (f : R -> R -> R)
    (fdiff : forall x y : R, x^+2 + y^+2 < 1 ->
        differentiable (fun z => f z y) x /\
        differentiable (fun z => f x z) y)
    (fbound : forall x y : R, x^+2 + y^+2 <= 1 -> `| f x y | <= 1)
    : exists x0 y0 : R, x0^+2 + y0^+2 < 1 /\ 
        ((fun x : R => f x y0)^`() x0)^+2 + ((fun y : R => f x0 y)^`() y0)^+2 <= 16.
Proof. Admitted.
