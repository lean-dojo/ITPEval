Require Import Reals.
Open Scope R.

Definition putnam_2022_b6_solution (f : R -> R) : Prop :=
  exists c : R,
    c >= 0 /\
    forall x : R, x > 0 -> f x = 1 / (1 + c * x).

Theorem putnam_2022_b6
    (f : R -> R)
    (hpos : forall x : R, x > 0 -> f x > 0)
    (hcont : forall x : R, x > 0 -> continuity_pt f x)
    : (forall x y : R,
        x > 0 ->
        y > 0 ->
        f (x * f y) + f (y * f x) = 1 + f (x + y)) <->
      putnam_2022_b6_solution f.
Proof. Admitted.
