(*
  Statement-only formalization of Thousand Theorems corpus artifact Q727102
  (thousand-theorems__rocq__Q727102), "Fermat's theorem (stationary points)":
  the totalized derivative of a real-valued function at a local extremum is
  zero, both on arbitrary real normed vector spaces and on the real line.
  This file contains no proof.
*)

From Stdlib Require Import Reals ClassicalDescription ClassicalEpsilon.

Set Universe Polymorphism.

Open Scope R_scope.

Record q727102_real_normed_vector_space : Type := {
  q727102_carrier : Type;
  q727102_zero : q727102_carrier;
  q727102_add :
    q727102_carrier -> q727102_carrier -> q727102_carrier;
  q727102_opp :
    q727102_carrier -> q727102_carrier;
  q727102_smul :
    R -> q727102_carrier -> q727102_carrier;
  q727102_norm :
    q727102_carrier -> R;
  q727102_add_assoc :
    forall x y z : q727102_carrier,
      q727102_add x (q727102_add y z) =
      q727102_add (q727102_add x y) z;
  q727102_add_comm :
    forall x y : q727102_carrier,
      q727102_add x y = q727102_add y x;
  q727102_add_zero :
    forall x : q727102_carrier,
      q727102_add x q727102_zero = x;
  q727102_add_opp :
    forall x : q727102_carrier,
      q727102_add x (q727102_opp x) = q727102_zero;
  q727102_smul_one :
    forall x : q727102_carrier,
      q727102_smul 1 x = x;
  q727102_smul_assoc :
    forall (r s : R) (x : q727102_carrier),
      q727102_smul r (q727102_smul s x) =
      q727102_smul (r * s) x;
  q727102_smul_add :
    forall (r : R) (x y : q727102_carrier),
      q727102_smul r (q727102_add x y) =
      q727102_add (q727102_smul r x) (q727102_smul r y);
  q727102_add_smul :
    forall (r s : R) (x : q727102_carrier),
      q727102_smul (r + s) x =
      q727102_add (q727102_smul r x) (q727102_smul s x);
  q727102_norm_nonneg :
    forall x : q727102_carrier,
      0 <= q727102_norm x;
  q727102_norm_eq_zero :
    forall x : q727102_carrier,
      q727102_norm x = 0 <-> x = q727102_zero;
  q727102_norm_triangle :
    forall x y : q727102_carrier,
      q727102_norm (q727102_add x y) <=
      q727102_norm x + q727102_norm y;
  q727102_norm_smul :
    forall (r : R) (x : q727102_carrier),
      q727102_norm (q727102_smul r x) =
      Rabs r * q727102_norm x
}.

Definition q727102_sub
    (E : q727102_real_normed_vector_space)
    (x y : q727102_carrier E) : q727102_carrier E :=
  q727102_add E x (q727102_opp E y).

Definition q727102_is_local_min
    (E : q727102_real_normed_vector_space)
    (f : q727102_carrier E -> R)
    (a : q727102_carrier E) : Prop :=
  exists radius : R,
    0 < radius /\
    forall x : q727102_carrier E,
      q727102_norm E (q727102_sub E x a) < radius ->
      f a <= f x.

Definition q727102_is_local_max
    (E : q727102_real_normed_vector_space)
    (f : q727102_carrier E -> R)
    (a : q727102_carrier E) : Prop :=
  exists radius : R,
    0 < radius /\
    forall x : q727102_carrier E,
      q727102_norm E (q727102_sub E x a) < radius ->
      f x <= f a.

Definition q727102_is_local_extr
    (E : q727102_real_normed_vector_space)
    (f : q727102_carrier E -> R)
    (a : q727102_carrier E) : Prop :=
  q727102_is_local_min E f a \/ q727102_is_local_max E f a.

Definition q727102_is_continuous_linear
    (E : q727102_real_normed_vector_space)
    (L : q727102_carrier E -> R) : Prop :=
  (forall x y : q727102_carrier E,
      L (q727102_add E x y) = L x + L y) /\
  (forall (r : R) (x : q727102_carrier E),
      L (q727102_smul E r x) = r * L x) /\
  exists bound : R,
    0 <= bound /\
    forall x : q727102_carrier E,
      Rabs (L x) <= bound * q727102_norm E x.

Definition q727102_has_fderiv_at
    (E : q727102_real_normed_vector_space)
    (f : q727102_carrier E -> R)
    (a : q727102_carrier E)
    (L : q727102_carrier E -> R) : Prop :=
  q727102_is_continuous_linear E L /\
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall h : q727102_carrier E,
        q727102_norm E h < delta ->
        Rabs
          (f (q727102_add E a h) - f a - L h) <=
        epsilon * q727102_norm E h.

Definition q727102_fderiv
    (E : q727102_real_normed_vector_space)
    (f : q727102_carrier E -> R)
    (a : q727102_carrier E) : q727102_carrier E -> R :=
  match excluded_middle_informative
          (exists L : q727102_carrier E -> R,
            q727102_has_fderiv_at E f a L) with
  | left _ =>
      epsilon
        (inhabits (fun _ : q727102_carrier E => 0))
        (fun L : q727102_carrier E -> R =>
          q727102_has_fderiv_at E f a L)
  | right _ => fun _ : q727102_carrier E => 0
  end.

Theorem IsLocalExtr_fderiv_eq_zero :
  forall (E : q727102_real_normed_vector_space)
         (f : q727102_carrier E -> R)
         (a : q727102_carrier E),
    q727102_is_local_extr E f a ->
    forall direction : q727102_carrier E,
      q727102_fderiv E f a direction = 0.
Admitted.

Definition q727102_is_local_extr_real
    (f : R -> R) (a : R) : Prop :=
  (exists radius : R,
      0 < radius /\
      forall x : R,
        Rabs (x - a) < radius ->
        f a <= f x) \/
  (exists radius : R,
      0 < radius /\
      forall x : R,
        Rabs (x - a) < radius ->
        f x <= f a).

Definition q727102_deriv
    (f : R -> R) (a : R) : R :=
  match excluded_middle_informative
          (exists derivative : R,
            derivable_pt_lim f a derivative) with
  | left _ =>
      epsilon
        (inhabits 0)
        (fun derivative : R =>
          derivable_pt_lim f a derivative)
  | right _ => 0
  end.

Theorem IsLocalExtr_deriv_eq_zero :
  forall (f : R -> R) (a : R),
    q727102_is_local_extr_real f a ->
    q727102_deriv f a = 0.
Admitted.
