(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1050932
  (thousand-theorems__rocq__Q1050932), "Hartogs's theorem": a function from
  an open subset of the complex plane squared to a complete second-countable
  complex normed space is jointly analytic when it is analytic separately in
  each complex coordinate. This file contains no proof.
*)

From Stdlib Require Import Reals Arith.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1050932_set (A : Type) : Type := A -> Prop.

Definition q1050932_complex : Type := (R * R)%type.
Definition q1050932_complex_pair : Type :=
  (q1050932_complex * q1050932_complex)%type.

Definition q1050932_czero : q1050932_complex := (0, 0).
Definition q1050932_cone : q1050932_complex := (1, 0).

Definition q1050932_cadd
    (z w : q1050932_complex) : q1050932_complex :=
  (fst z + fst w, snd z + snd w).

Definition q1050932_cneg
    (z : q1050932_complex) : q1050932_complex :=
  (- fst z, - snd z).

Definition q1050932_csub
    (z w : q1050932_complex) : q1050932_complex :=
  q1050932_cadd z (q1050932_cneg w).

Definition q1050932_cmul
    (z w : q1050932_complex) : q1050932_complex :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition q1050932_cmodulus
    (z : q1050932_complex) : R :=
  sqrt (fst z * fst z + snd z * snd z).

Definition q1050932_pair_zero : q1050932_complex_pair :=
  (q1050932_czero, q1050932_czero).

Definition q1050932_pair_add
    (x y : q1050932_complex_pair) : q1050932_complex_pair :=
  (q1050932_cadd (fst x) (fst y),
   q1050932_cadd (snd x) (snd y)).

Definition q1050932_pair_smul
    (a : q1050932_complex)
    (x : q1050932_complex_pair) : q1050932_complex_pair :=
  (q1050932_cmul a (fst x), q1050932_cmul a (snd x)).

Definition q1050932_pair_sub
    (x y : q1050932_complex_pair) : q1050932_complex_pair :=
  (q1050932_csub (fst x) (fst y),
   q1050932_csub (snd x) (snd y)).

Definition q1050932_pair_norm
    (x : q1050932_complex_pair) : R :=
  Rmax (q1050932_cmodulus (fst x)) (q1050932_cmodulus (snd x)).

Record q1050932_normed_complex_vector_space (E : Type) : Type := {
  q1050932_zero : E;
  q1050932_add : E -> E -> E;
  q1050932_neg : E -> E;
  q1050932_smul : q1050932_complex -> E -> E;
  q1050932_norm : E -> R;

  q1050932_add_assoc :
    forall x y z : E,
      q1050932_add x (q1050932_add y z) =
      q1050932_add (q1050932_add x y) z;
  q1050932_add_comm :
    forall x y : E, q1050932_add x y = q1050932_add y x;
  q1050932_add_zero :
    forall x : E, q1050932_add x q1050932_zero = x;
  q1050932_add_neg :
    forall x : E,
      q1050932_add x (q1050932_neg x) = q1050932_zero;

  q1050932_one_smul :
    forall x : E, q1050932_smul q1050932_cone x = x;
  q1050932_mul_smul :
    forall (a b : q1050932_complex) (x : E),
      q1050932_smul (q1050932_cmul a b) x =
      q1050932_smul a (q1050932_smul b x);
  q1050932_add_smul :
    forall (a b : q1050932_complex) (x : E),
      q1050932_smul (q1050932_cadd a b) x =
      q1050932_add
        (q1050932_smul a x) (q1050932_smul b x);
  q1050932_smul_add :
    forall (a : q1050932_complex) (x y : E),
      q1050932_smul a (q1050932_add x y) =
      q1050932_add
        (q1050932_smul a x) (q1050932_smul a y);
  q1050932_zero_smul :
    forall x : E, q1050932_smul q1050932_czero x = q1050932_zero;
  q1050932_smul_zero :
    forall a : q1050932_complex,
      q1050932_smul a q1050932_zero = q1050932_zero;

  q1050932_norm_nonnegative :
    forall x : E, 0 <= q1050932_norm x;
  q1050932_norm_eq_zero :
    forall x : E, q1050932_norm x = 0 <-> x = q1050932_zero;
  q1050932_norm_neg :
    forall x : E, q1050932_norm (q1050932_neg x) = q1050932_norm x;
  q1050932_norm_add_le :
    forall x y : E,
      q1050932_norm (q1050932_add x y) <=
      q1050932_norm x + q1050932_norm y;
  q1050932_norm_smul :
    forall (a : q1050932_complex) (x : E),
      q1050932_norm (q1050932_smul a x) =
      q1050932_cmodulus a * q1050932_norm x
}.

Arguments q1050932_zero {E} _.
Arguments q1050932_add {E} _ _ _.
Arguments q1050932_neg {E} _ _.
Arguments q1050932_smul {E} _ _ _.
Arguments q1050932_norm {E} _ _.

Definition q1050932_sub
    {E : Type}
    (V : q1050932_normed_complex_vector_space E)
    (x y : E) : E :=
  q1050932_add V x (q1050932_neg V y).

Definition q1050932_dist
    {E : Type}
    (V : q1050932_normed_complex_vector_space E)
    (x y : E) : R :=
  q1050932_norm V (q1050932_sub V x y).

Definition q1050932_sequence_converges
    {E : Type}
    (V : q1050932_normed_complex_vector_space E)
    (u : nat -> E) (limit : E) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists N : nat, forall n : nat, (N <= n)%nat ->
      q1050932_dist V (u n) limit < epsilon.

Definition q1050932_sequence_cauchy
    {E : Type}
    (V : q1050932_normed_complex_vector_space E)
    (u : nat -> E) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists N : nat, forall m n : nat,
      (N <= m)%nat ->
      (N <= n)%nat ->
      q1050932_dist V (u m) (u n) < epsilon.

Definition q1050932_complete
    {E : Type}
    (V : q1050932_normed_complex_vector_space E) : Prop :=
  forall u : nat -> E,
    q1050932_sequence_cauchy V u ->
    exists limit : E, q1050932_sequence_converges V u limit.

Definition q1050932_open_in_E
    {E : Type}
    (V : q1050932_normed_complex_vector_space E)
    (U : q1050932_set E) : Prop :=
  forall x : E, U x ->
    exists radius : R, 0 < radius /\
      forall y : E, q1050932_dist V y x < radius -> U y.

Definition q1050932_second_countable
    {E : Type}
    (V : q1050932_normed_complex_vector_space E) : Prop :=
  exists basis : nat -> q1050932_set E,
    (forall n : nat, q1050932_open_in_E V (basis n)) /\
    forall (U : q1050932_set E) (x : E),
      q1050932_open_in_E V U ->
      U x ->
      exists n : nat,
        basis n x /\
        forall y : E, basis n y -> U y.

Record q1050932_scalar_linear_map
    {E : Type}
    (V : q1050932_normed_complex_vector_space E) : Type := {
  q1050932_scalar_linear_apply : q1050932_complex -> E;
  q1050932_scalar_linear_add :
    forall z w : q1050932_complex,
      q1050932_scalar_linear_apply (q1050932_cadd z w) =
      q1050932_add V
        (q1050932_scalar_linear_apply z)
        (q1050932_scalar_linear_apply w);
  q1050932_scalar_linear_smul :
    forall z w : q1050932_complex,
      q1050932_scalar_linear_apply (q1050932_cmul z w) =
      q1050932_smul V z (q1050932_scalar_linear_apply w);
  q1050932_scalar_linear_bounded :
    exists bound : R,
      0 <= bound /\
      forall z : q1050932_complex,
        q1050932_norm V (q1050932_scalar_linear_apply z) <=
        bound * q1050932_cmodulus z
}.

Arguments q1050932_scalar_linear_apply {E V} _ _.

Record q1050932_pair_linear_map
    {E : Type}
    (V : q1050932_normed_complex_vector_space E) : Type := {
  q1050932_pair_linear_apply : q1050932_complex_pair -> E;
  q1050932_pair_linear_add :
    forall x y : q1050932_complex_pair,
      q1050932_pair_linear_apply (q1050932_pair_add x y) =
      q1050932_add V
        (q1050932_pair_linear_apply x)
        (q1050932_pair_linear_apply y);
  q1050932_pair_linear_smul :
    forall (a : q1050932_complex) (x : q1050932_complex_pair),
      q1050932_pair_linear_apply (q1050932_pair_smul a x) =
      q1050932_smul V a (q1050932_pair_linear_apply x);
  q1050932_pair_linear_bounded :
    exists bound : R,
      0 <= bound /\
      forall x : q1050932_complex_pair,
        q1050932_norm V (q1050932_pair_linear_apply x) <=
        bound * q1050932_pair_norm x
}.

Arguments q1050932_pair_linear_apply {E V} _ _.

Definition q1050932_has_scalar_frechet_derivative_at
    {E : Type}
    (V : q1050932_normed_complex_vector_space E)
    (f : q1050932_complex -> E)
    (x : q1050932_complex)
    (D : q1050932_scalar_linear_map V) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists delta : R, 0 < delta /\
      forall h : q1050932_complex,
        q1050932_cmodulus h < delta ->
        q1050932_norm V
          (q1050932_sub V
            (q1050932_sub V (f (q1050932_cadd x h)) (f x))
            (q1050932_scalar_linear_apply D h)) <=
        epsilon * q1050932_cmodulus h.

Definition q1050932_scalar_differentiable_at
    {E : Type}
    (V : q1050932_normed_complex_vector_space E)
    (f : q1050932_complex -> E)
    (x : q1050932_complex) : Prop :=
  exists D : q1050932_scalar_linear_map V,
    @q1050932_has_scalar_frechet_derivative_at E V f x D.

Definition q1050932_scalar_analytic_at
    {E : Type}
    (V : q1050932_normed_complex_vector_space E)
    (f : q1050932_complex -> E)
    (x : q1050932_complex) : Prop :=
  exists radius : R, 0 < radius /\
    forall y : q1050932_complex,
      q1050932_cmodulus (q1050932_csub y x) < radius ->
      @q1050932_scalar_differentiable_at E V f y.

Definition q1050932_has_pair_frechet_derivative_at
    {E : Type}
    (V : q1050932_normed_complex_vector_space E)
    (f : q1050932_complex_pair -> E)
    (x : q1050932_complex_pair)
    (D : q1050932_pair_linear_map V) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists delta : R, 0 < delta /\
      forall h : q1050932_complex_pair,
        q1050932_pair_norm h < delta ->
        q1050932_norm V
          (q1050932_sub V
            (q1050932_sub V (f (q1050932_pair_add x h)) (f x))
            (q1050932_pair_linear_apply D h)) <=
        epsilon * q1050932_pair_norm h.

Definition q1050932_pair_differentiable_at
    {E : Type}
    (V : q1050932_normed_complex_vector_space E)
    (f : q1050932_complex_pair -> E)
    (x : q1050932_complex_pair) : Prop :=
  exists D : q1050932_pair_linear_map V,
    @q1050932_has_pair_frechet_derivative_at E V f x D.

Definition q1050932_pair_analytic_at
    {E : Type}
    (V : q1050932_normed_complex_vector_space E)
    (f : q1050932_complex_pair -> E)
    (x : q1050932_complex_pair) : Prop :=
  exists radius : R, 0 < radius /\
    forall y : q1050932_complex_pair,
      q1050932_pair_norm (q1050932_pair_sub y x) < radius ->
      @q1050932_pair_differentiable_at E V f y.

Definition q1050932_pair_open
    (S : q1050932_set q1050932_complex_pair) : Prop :=
  forall x : q1050932_complex_pair, S x ->
    exists radius : R, 0 < radius /\
      forall y : q1050932_complex_pair,
        q1050932_pair_norm (q1050932_pair_sub y x) < radius ->
        S y.

Definition q1050932_pair_analytic_on_nhd
    {E : Type}
    (V : q1050932_normed_complex_vector_space E)
    (f : q1050932_complex_pair -> E)
    (S : q1050932_set q1050932_complex_pair) : Prop :=
  forall x : q1050932_complex_pair,
    S x -> @q1050932_pair_analytic_at E V f x.

Module Pair.

Theorem hartogs :
  forall (E : Type)
         (V : q1050932_normed_complex_vector_space E)
         (f : q1050932_complex_pair -> E)
         (S : q1050932_set q1050932_complex_pair),
    q1050932_complete V ->
    q1050932_second_countable V ->
    q1050932_pair_open S ->
    (forall c0 c1 : q1050932_complex,
      S (c0, c1) ->
      @q1050932_scalar_analytic_at E V (fun z0 => f (z0, c1)) c0) ->
    (forall c0 c1 : q1050932_complex,
      S (c0, c1) ->
      @q1050932_scalar_analytic_at E V (fun z1 => f (c0, z1)) c1) ->
    @q1050932_pair_analytic_on_nhd E V f S.
Admitted.

End Pair.
