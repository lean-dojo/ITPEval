(*
  Statement-only formalization of Thousand Theorems corpus artifact Q189136
  (thousand-theorems__rocq__Q189136), "Mean value theorem": Lagrange's and
  Cauchy's mean value theorems for real functions continuous on a closed
  interval and differentiable on its interior. This file contains no proof.
*)

From Stdlib Require Import Reals ClassicalDescription ClassicalEpsilon.

Open Scope R_scope.

Definition q189136_set : Type := R -> Prop.

Definition q189136_closed_interval
    (a b : R) : q189136_set :=
  fun x : R => a <= x /\ x <= b.

Definition q189136_open_interval
    (a b : R) : q189136_set :=
  fun x : R => a < x /\ x < b.

Definition q189136_continuous_within_at
    (f : R -> R) (s : q189136_set) (x : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : R,
        s y ->
        Rabs (y - x) < delta ->
        Rabs (f y - f x) < epsilon.

Definition q189136_continuous_on
    (f : R -> R) (s : q189136_set) : Prop :=
  forall x : R,
    s x ->
    q189136_continuous_within_at f s x.

Definition q189136_deriv
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

Definition q189136_differentiable_on
    (f : R -> R) (s : q189136_set) : Prop :=
  forall x : R,
    s x ->
    exists derivative : R,
      derivable_pt_lim f x derivative.

Theorem exists_ratio_deriv_eq_ratio_slope :
  forall (f g : R -> R) (a b : R),
    a < b ->
    q189136_continuous_on f
      (q189136_closed_interval a b) ->
    q189136_continuous_on g
      (q189136_closed_interval a b) ->
    q189136_differentiable_on f
      (q189136_open_interval a b) ->
    q189136_differentiable_on g
      (q189136_open_interval a b) ->
    exists c : R,
      q189136_open_interval a b c /\
      (g b - g a) * q189136_deriv f c =
      (f b - f a) * q189136_deriv g c.
Admitted.

Theorem exists_deriv_eq_slope :
  forall (f : R -> R) (a b : R),
    a < b ->
    q189136_continuous_on f
      (q189136_closed_interval a b) ->
    q189136_differentiable_on f
      (q189136_open_interval a b) ->
    exists c : R,
      q189136_open_interval a b c /\
      q189136_deriv f c =
      (f b - f a) / (b - a).
Admitted.
