From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals exp sequences.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Variable R : realType.
Definition putnam_1975_a3_rpow (x r : R) : R :=
  if x == 0 then 0 else expR (r * ln x).

Definition putnam_1975_a3_solution : ((R * R * R) -> (R * R * R)) * ((R * R * R) -> (R * R * R)) :=
    (fun xyz => let '(a, b, c) := xyz in
      let x := putnam_1975_a3_rpow (a / b) (1 / (b - a)) in
      (x, putnam_1975_a3_rpow (1 - putnam_1975_a3_rpow x b) (1 / b), 0),
    fun xyz => let '(a, b, c) := xyz in
      let z := putnam_1975_a3_rpow (b / c) (1 / (c - b)) in
      (0, putnam_1975_a3_rpow (1 - putnam_1975_a3_rpow z b) (1 / b), z)).
Theorem putnam_1975_a3
    (a b c : R)
    (hi : 0 < a /\ a < b < c)
    (P : (R * R * R) -> Prop := fun xyz: R * R * R => let '(x, y, z) := xyz in
      (x >= 0 /\ y >= 0 /\ z >= 0 /\
       putnam_1975_a3_rpow x b + putnam_1975_a3_rpow y b + putnam_1975_a3_rpow z b = 1))
    (f : (R * R * R) -> R := fun xyz: R * R * R => let '(x, y, z) := xyz in
      putnam_1975_a3_rpow x a + putnam_1975_a3_rpow y b + putnam_1975_a3_rpow z c)
    : (P ((fst putnam_1975_a3_solution) (a, b, c)) /\ forall x y z : R, P (x, y, z) ->
    f (x, y, z) <= f ((fst putnam_1975_a3_solution) (a, b, c))) /\
    (P ((snd putnam_1975_a3_solution) (a, b, c)) /\ forall x y z : R, P (x, y, z) ->
    f (x, y, z) >= f ((snd putnam_1975_a3_solution) (a, b, c))).
Proof. Admitted.
