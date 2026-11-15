(*
  Statement-only formalization of Thousand Theorems corpus artifact Q967972
  (thousand-theorems__rocq__Q967972), "Open mapping theorem (complex
  analysis)": an analytic complex-valued function on a preconnected subset
  of a complex normed vector space is either constant there or maps every
  ambient-open set contained in that subset to an open subset of the complex
  plane.
  This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q967972_set (A : Type) : Type := A -> Prop.

Definition q967972_complex : Type := (R * R)%type.

Definition q967972_czero : q967972_complex := (0, 0).
Definition q967972_cone : q967972_complex := (1, 0).

Definition q967972_cadd
    (z w : q967972_complex) : q967972_complex :=
  (fst z + fst w, snd z + snd w).

Definition q967972_cneg
    (z : q967972_complex) : q967972_complex :=
  (- fst z, - snd z).

Definition q967972_csub
    (z w : q967972_complex) : q967972_complex :=
  q967972_cadd z (q967972_cneg w).

Definition q967972_cmul
    (z w : q967972_complex) : q967972_complex :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition q967972_cmodulus
    (z : q967972_complex) : R :=
  sqrt (fst z * fst z + snd z * snd z).

Record q967972_normed_complex_vector_space (E : Type) : Type := {
  q967972_zero : E;
  q967972_add : E -> E -> E;
  q967972_neg : E -> E;
  q967972_smul : q967972_complex -> E -> E;
  q967972_norm : E -> R;

  q967972_add_assoc :
    forall x y z : E,
      q967972_add x (q967972_add y z) =
      q967972_add (q967972_add x y) z;
  q967972_add_comm :
    forall x y : E, q967972_add x y = q967972_add y x;
  q967972_add_zero :
    forall x : E, q967972_add x q967972_zero = x;
  q967972_add_neg :
    forall x : E, q967972_add x (q967972_neg x) = q967972_zero;

  q967972_one_smul :
    forall x : E, q967972_smul q967972_cone x = x;
  q967972_mul_smul :
    forall (a b : q967972_complex) (x : E),
      q967972_smul (q967972_cmul a b) x =
      q967972_smul a (q967972_smul b x);
  q967972_add_smul :
    forall (a b : q967972_complex) (x : E),
      q967972_smul (q967972_cadd a b) x =
      q967972_add
        (q967972_smul a x) (q967972_smul b x);
  q967972_smul_add :
    forall (a : q967972_complex) (x y : E),
      q967972_smul a (q967972_add x y) =
      q967972_add
        (q967972_smul a x) (q967972_smul a y);
  q967972_zero_smul :
    forall x : E, q967972_smul q967972_czero x = q967972_zero;
  q967972_smul_zero :
    forall a : q967972_complex,
      q967972_smul a q967972_zero = q967972_zero;

  q967972_norm_nonnegative :
    forall x : E, 0 <= q967972_norm x;
  q967972_norm_eq_zero :
    forall x : E, q967972_norm x = 0 <-> x = q967972_zero;
  q967972_norm_neg :
    forall x : E,
      q967972_norm (q967972_neg x) = q967972_norm x;
  q967972_norm_add_le :
    forall x y : E,
      q967972_norm (q967972_add x y) <=
      q967972_norm x + q967972_norm y;
  q967972_norm_smul :
    forall (a : q967972_complex) (x : E),
      q967972_norm (q967972_smul a x) =
      q967972_cmodulus a * q967972_norm x
}.

Arguments q967972_zero {E} _.
Arguments q967972_add {E} _ _ _.
Arguments q967972_neg {E} _ _.
Arguments q967972_smul {E} _ _ _.
Arguments q967972_norm {E} _ _.

Definition q967972_sub
    {E : Type}
    (V : q967972_normed_complex_vector_space E)
    (x y : E) : E :=
  q967972_add V x (q967972_neg V y).

Record q967972_continuous_complex_linear_map
    {E : Type}
    (V : q967972_normed_complex_vector_space E) : Type := {
  q967972_linear_apply : E -> q967972_complex;
  q967972_linear_add :
    forall x y : E,
      q967972_linear_apply (q967972_add V x y) =
      q967972_cadd
        (q967972_linear_apply x) (q967972_linear_apply y);
  q967972_linear_smul :
    forall (a : q967972_complex) (x : E),
      q967972_linear_apply (q967972_smul V a x) =
      q967972_cmul a (q967972_linear_apply x);
  q967972_linear_bounded :
    exists bound : R,
      0 <= bound /\
      forall x : E,
        q967972_cmodulus (q967972_linear_apply x) <=
        bound * q967972_norm V x
}.

Arguments q967972_linear_apply {E V} _ _.

Definition q967972_has_frechet_derivative_at
    {E : Type}
    (V : q967972_normed_complex_vector_space E)
    (f : E -> q967972_complex)
    (x : E)
    (D : q967972_continuous_complex_linear_map V) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall h : E,
        q967972_norm V h < delta ->
        q967972_cmodulus
          (q967972_csub
            (q967972_csub
              (f (q967972_add V x h)) (f x))
            (q967972_linear_apply D h)) <=
        epsilon * q967972_norm V h.

Definition q967972_complex_differentiable_at
    {E : Type}
    (V : q967972_normed_complex_vector_space E)
  (f : E -> q967972_complex)
  (x : E) : Prop :=
  exists D : q967972_continuous_complex_linear_map V,
    @q967972_has_frechet_derivative_at E V f x D.

Definition q967972_analytic_at
    {E : Type}
    (V : q967972_normed_complex_vector_space E)
    (f : E -> q967972_complex)
    (x : E) : Prop :=
  exists radius : R,
    0 < radius /\
    forall y : E,
      q967972_norm V (q967972_sub V y x) < radius ->
      q967972_complex_differentiable_at V f y.

Definition q967972_analytic_on_nhd
    {E : Type}
    (V : q967972_normed_complex_vector_space E)
    (f : E -> q967972_complex)
    (U : q967972_set E) : Prop :=
  forall x : E, U x -> q967972_analytic_at V f x.

Definition q967972_open
    {E : Type}
    (V : q967972_normed_complex_vector_space E)
    (S : q967972_set E) : Prop :=
  forall x : E,
    S x ->
    exists radius : R,
      0 < radius /\
      forall y : E,
        q967972_norm V (q967972_sub V y x) < radius ->
        S y.

Definition q967972_complex_open
    (S : q967972_set q967972_complex) : Prop :=
  forall z : q967972_complex,
    S z ->
    exists radius : R,
      0 < radius /\
      forall w : q967972_complex,
        q967972_cmodulus (q967972_csub w z) < radius ->
        S w.

Definition q967972_relatively_open
    {E : Type}
    (V : q967972_normed_complex_vector_space E)
    (U S : q967972_set E) : Prop :=
  exists ambient : q967972_set E,
    q967972_open V ambient /\
    forall x : E, S x <-> U x /\ ambient x.

Definition q967972_is_preconnected
    {E : Type}
    (V : q967972_normed_complex_vector_space E)
    (U : q967972_set E) : Prop :=
  forall left right : q967972_set E,
    q967972_relatively_open V U left ->
    q967972_relatively_open V U right ->
    (forall x : E, U x <-> left x \/ right x) ->
    (forall x : E, ~ (left x /\ right x)) ->
    (forall x : E, ~ left x) \/ (forall x : E, ~ right x).

Definition q967972_included
    {A : Type}
    (S T : q967972_set A) : Prop :=
  forall x : A, S x -> T x.

Definition q967972_image
    {A B : Type}
    (f : A -> B)
    (S : q967972_set A) : q967972_set B :=
  fun y => exists x : A, S x /\ f x = y.

Theorem AnalyticOnNhd_is_constant_or_isOpen :
  forall (E : Type)
         (V : q967972_normed_complex_vector_space E)
         (U : q967972_set E)
         (g : E -> q967972_complex),
    q967972_analytic_on_nhd V g U ->
    q967972_is_preconnected V U ->
    (exists w : q967972_complex,
      forall z : E, U z -> g z = w) \/
    (forall s : q967972_set E,
      q967972_included s U ->
      q967972_open V s ->
      q967972_complex_open (q967972_image g s)).
Admitted.
