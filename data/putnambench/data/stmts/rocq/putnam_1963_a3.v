(* Statement-only formalization of PutnamBench artifact putnam_1963_a3:
   the integral formula for an initial-value problem involving the iterated
   Euler differential operator. This file contains no proof. *)

From Stdlib Require Import
  Reals
  ClassicalDescription
  ClassicalEpsilon
  Arith.Factorial
  Arith.PeanoNat.

Open Scope R_scope.

Definition total_derivative (f : R -> R) (x : R) : R :=
  match excluded_middle_informative
          (exists value : R, derivable_pt_lim f x value) with
  | left _ =>
      epsilon (inhabits 0)
        (fun value : R => derivable_pt_lim f x value)
  | right _ => 0
  end.

Fixpoint iterated_derivative
    (n : nat) (f : R -> R) : R -> R :=
  match n with
  | O => f
  | S k => total_derivative (iterated_derivative k f)
  end.

Definition putnam_1963_a3_solution
    (f : R -> R) (n : nat) (x t : R) : R :=
  ((x - t) ^ (Nat.pred n) * f t) /
  (INR (fact (Nat.pred n)) * t ^ n).

Definition riemann_integral_value
    (f : R -> R) (a b value : R) : Prop :=
  exists integrable : Riemann_integrable f a b,
    RiemannInt integrable = value.

Definition continuous_on_from_one (f : R -> R) : Prop :=
  forall x : R,
    1 <= x ->
    forall epsilon : R,
      0 < epsilon ->
      exists delta : R,
        0 < delta /\
        forall z : R,
          1 <= z ->
          Rabs (z - x) < delta ->
          Rabs (f z - f x) < epsilon.

Definition continuously_differentiable_on_from_one
    (n : nat) (y : R -> R) : Prop :=
  forall k : nat,
    (k <= n)%nat ->
    continuous_on_from_one (iterated_derivative k y) /\
    forall x : R,
      1 <= x ->
      (k < n)%nat ->
      derivable_pt_lim
        (iterated_derivative k y) x
        (iterated_derivative (S k) y x).

Definition continuously_differentiable_at
    (n : nat) (y : R -> R) (a : R) : Prop :=
  exists radius : R,
    0 < radius /\
    forall (k : nat) (x : R),
      (k <= n)%nat ->
      Rabs (x - a) < radius ->
      continuity_pt (iterated_derivative k y) x /\
      ((k < n)%nat ->
       derivable_pt_lim
         (iterated_derivative k y) x
         (iterated_derivative (S k) y x)).

Theorem putnam_1963_a3 :
  forall
    (P : nat -> (R -> R) -> (R -> R))
    (n : nat)
    (f y : R -> R),
    ((forall u : R -> R, P 0%nat u = u) /\
     forall (i : nat) (u : R -> R),
       P (S i) u =
       P i
         (fun x : R =>
            x * total_derivative u x - INR i * u x)) ->
    (0 < n)%nat ->
    continuous_on_from_one f ->
    continuously_differentiable_on_from_one n y ->
    continuously_differentiable_at n y 1 ->
    (((forall i : nat,
         (i < n)%nat ->
         iterated_derivative i y 1 = 0) /\
      (forall x : R,
         1 <= x ->
         P n y x = f x)) <->
     (forall x : R,
        1 <= x ->
        riemann_integral_value
          (putnam_1963_a3_solution f n x) 1 x (y x))).
Admitted.
