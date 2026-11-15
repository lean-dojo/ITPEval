(*
  Statement-only formalization of Thousand Theorems corpus artifact Q4378868
  (thousand-theorems__rocq__Q4378868), "Phragmén–Lindelöf theorem": the
  Phragmén–Lindelöf principle bounds a complex-differentiable
  normed-space-valued function throughout a closed horizontal strip from its
  boundary bound, under a controlled double-exponential growth condition.
  This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q4378868_complex : Type := (R * R)%type.

Definition q4378868_czero : q4378868_complex := (0, 0).
Definition q4378868_cone : q4378868_complex := (1, 0).

Definition q4378868_cadd
    (z w : q4378868_complex) : q4378868_complex :=
  (fst z + fst w, snd z + snd w).

Definition q4378868_cneg
    (z : q4378868_complex) : q4378868_complex :=
  (- fst z, - snd z).

Definition q4378868_csub
    (z w : q4378868_complex) : q4378868_complex :=
  q4378868_cadd z (q4378868_cneg w).

Definition q4378868_cmul
    (z w : q4378868_complex) : q4378868_complex :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition q4378868_cmodulus
    (z : q4378868_complex) : R :=
  sqrt (fst z * fst z + snd z * snd z).

Definition q4378868_horizontal_strip
    (a b : R) (z : q4378868_complex) : Prop :=
  a < snd z /\ snd z < b.

Record q4378868_normed_complex_vector_space (E : Type) : Type := {
  q4378868_zero : E;
  q4378868_add : E -> E -> E;
  q4378868_neg : E -> E;
  q4378868_smul : q4378868_complex -> E -> E;
  q4378868_norm : E -> R;

  q4378868_add_assoc :
    forall x y z : E,
      q4378868_add x (q4378868_add y z) =
      q4378868_add (q4378868_add x y) z;
  q4378868_add_comm :
    forall x y : E, q4378868_add x y = q4378868_add y x;
  q4378868_add_zero :
    forall x : E, q4378868_add x q4378868_zero = x;
  q4378868_add_neg :
    forall x : E,
      q4378868_add x (q4378868_neg x) = q4378868_zero;

  q4378868_one_smul :
    forall x : E, q4378868_smul q4378868_cone x = x;
  q4378868_mul_smul :
    forall (a b : q4378868_complex) (x : E),
      q4378868_smul (q4378868_cmul a b) x =
      q4378868_smul a (q4378868_smul b x);
  q4378868_add_smul :
    forall (a b : q4378868_complex) (x : E),
      q4378868_smul (q4378868_cadd a b) x =
      q4378868_add
        (q4378868_smul a x) (q4378868_smul b x);
  q4378868_smul_add :
    forall (a : q4378868_complex) (x y : E),
      q4378868_smul a (q4378868_add x y) =
      q4378868_add
        (q4378868_smul a x) (q4378868_smul a y);
  q4378868_zero_smul :
    forall x : E,
      q4378868_smul q4378868_czero x = q4378868_zero;
  q4378868_smul_zero :
    forall a : q4378868_complex,
      q4378868_smul a q4378868_zero = q4378868_zero;

  q4378868_norm_nonnegative :
    forall x : E, 0 <= q4378868_norm x;
  q4378868_norm_eq_zero :
    forall x : E,
      q4378868_norm x = 0 <-> x = q4378868_zero;
  q4378868_norm_add_le :
    forall x y : E,
      q4378868_norm (q4378868_add x y) <=
      q4378868_norm x + q4378868_norm y;
  q4378868_norm_smul :
    forall (a : q4378868_complex) (x : E),
      q4378868_norm (q4378868_smul a x) =
      q4378868_cmodulus a * q4378868_norm x
}.

Arguments q4378868_zero {E} _.
Arguments q4378868_add {E} _ _ _.
Arguments q4378868_neg {E} _ _.
Arguments q4378868_smul {E} _ _ _.
Arguments q4378868_norm {E} _ _.

Definition q4378868_sub
    {E : Type}
    (V : q4378868_normed_complex_vector_space E)
    (x y : E) : E :=
  q4378868_add V x (q4378868_neg V y).

Record q4378868_complex_linear_map
    {E : Type}
    (V : q4378868_normed_complex_vector_space E) : Type := {
  q4378868_linear_apply : q4378868_complex -> E;
  q4378868_linear_add :
    forall z w : q4378868_complex,
      q4378868_linear_apply (q4378868_cadd z w) =
      q4378868_add V
        (q4378868_linear_apply z) (q4378868_linear_apply w);
  q4378868_linear_smul :
    forall z w : q4378868_complex,
      q4378868_linear_apply (q4378868_cmul z w) =
      q4378868_smul V z (q4378868_linear_apply w);
  q4378868_linear_bounded :
    exists bound : R,
      0 <= bound /\
      forall z : q4378868_complex,
        q4378868_norm V (q4378868_linear_apply z) <=
        bound * q4378868_cmodulus z
}.

Arguments q4378868_linear_apply {E V} _ _.

Definition q4378868_closure
    (S : q4378868_complex -> Prop)
    (z : q4378868_complex) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists w : q4378868_complex,
      S w /\
      q4378868_cmodulus (q4378868_csub w z) < epsilon.

Definition q4378868_continuous_within_at
    {E : Type}
    (V : q4378868_normed_complex_vector_space E)
    (f : q4378868_complex -> E)
    (S : q4378868_complex -> Prop)
    (z : q4378868_complex) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall w : q4378868_complex,
        S w ->
        q4378868_cmodulus (q4378868_csub w z) < delta ->
        q4378868_norm V
          (q4378868_sub V (f w) (f z)) < epsilon.

Definition q4378868_continuous_on
    {E : Type}
    (V : q4378868_normed_complex_vector_space E)
    (f : q4378868_complex -> E)
    (S : q4378868_complex -> Prop) : Prop :=
  forall z : q4378868_complex,
    S z -> q4378868_continuous_within_at V f S z.

Definition q4378868_has_frechet_deriv_within_at
    {E : Type}
    (V : q4378868_normed_complex_vector_space E)
    (f : q4378868_complex -> E)
    (S : q4378868_complex -> Prop)
    (z : q4378868_complex)
    (D : q4378868_complex_linear_map V) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall w : q4378868_complex,
        S w ->
        q4378868_cmodulus (q4378868_csub w z) < delta ->
        q4378868_norm V
          (q4378868_sub V
            (q4378868_sub V (f w) (f z))
            (q4378868_linear_apply D (q4378868_csub w z))) <=
        epsilon * q4378868_cmodulus (q4378868_csub w z).

Definition q4378868_differentiable_on
    {E : Type}
    (V : q4378868_normed_complex_vector_space E)
    (f : q4378868_complex -> E)
    (S : q4378868_complex -> Prop) : Prop :=
  forall z : q4378868_complex,
    S z ->
    exists D : q4378868_complex_linear_map V,
      @q4378868_has_frechet_deriv_within_at E V f S z D.

Definition q4378868_diff_cont_on_closure
    {E : Type}
    (V : q4378868_normed_complex_vector_space E)
    (f : q4378868_complex -> E)
    (S : q4378868_complex -> Prop) : Prop :=
  q4378868_differentiable_on V f S /\
  q4378868_continuous_on V f (q4378868_closure S).

Definition q4378868_double_exponential_growth
    {E : Type}
    (V : q4378868_normed_complex_vector_space E)
    (f : q4378868_complex -> E)
    (a b : R) : Prop :=
  exists c : R,
    c < PI / (b - a) /\
    exists B A threshold : R,
      0 < A /\
      forall w : q4378868_complex,
        threshold <= Rabs (fst w) ->
        q4378868_horizontal_strip a b w ->
        q4378868_norm V (f w) <=
        A * exp (B * exp (c * Rabs (fst w))).

Module PhragmenLindelof.

Theorem horizontal_strip :
  forall (E : Type)
         (V : q4378868_normed_complex_vector_space E)
         (a b C : R)
         (f : q4378868_complex -> E)
         (z : q4378868_complex),
    q4378868_diff_cont_on_closure V f
      (q4378868_horizontal_strip a b) ->
    q4378868_double_exponential_growth V f a b ->
    (forall w : q4378868_complex,
      snd w = a -> q4378868_norm V (f w) <= C) ->
    (forall w : q4378868_complex,
      snd w = b -> q4378868_norm V (f w) <= C) ->
    a <= snd z ->
    snd z <= b ->
    q4378868_norm V (f z) <= C.
Admitted.

End PhragmenLindelof.
