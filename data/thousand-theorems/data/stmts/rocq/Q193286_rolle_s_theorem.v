(*
  Statement-only formalization of Thousand Theorems corpus artifact Q193286
  (thousand-theorems__rocq__Q193286), "Rolle's theorem": a continuous real
  function with equal values at the endpoints of a nondegenerate closed
  interval has derivative zero at some interior point, where the derivative
  is totalized to zero at nondifferentiable points. This file contains no
  proof.
*)

From Stdlib Require Import Reals ClassicalDescription ClassicalEpsilon.

Open Scope R_scope.

Definition q193286_set : Type := R -> Prop.

Definition q193286_closed_interval
    (a b : R) : q193286_set :=
  fun x : R => a <= x /\ x <= b.

Definition q193286_open_interval
    (a b : R) : q193286_set :=
  fun x : R => a < x /\ x < b.

Definition q193286_continuous_within_at
    (f : R -> R) (s : q193286_set) (x : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : R,
        s y ->
        Rabs (y - x) < delta ->
        Rabs (f y - f x) < epsilon.

Definition q193286_continuous_on
    (f : R -> R) (s : q193286_set) : Prop :=
  forall x : R,
    s x ->
    q193286_continuous_within_at f s x.

Definition q193286_deriv
    (f : R -> R) (x : R) : R :=
  match excluded_middle_informative
          (exists derivative : R,
            derivable_pt_lim f x derivative) with
  | left _ =>
      epsilon (inhabits 0)
        (fun derivative : R =>
          derivable_pt_lim f x derivative)
  | right _ => 0
  end.

Theorem exists_deriv_eq_zero :
  forall (f : R -> R) (a b : R),
    a < b ->
    q193286_continuous_on f
      (q193286_closed_interval a b) ->
    f a = f b ->
    exists c : R,
      q193286_open_interval a b c /\
      q193286_deriv f c = 0.
Admitted.
