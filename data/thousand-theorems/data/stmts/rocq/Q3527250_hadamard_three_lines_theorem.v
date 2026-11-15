(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527250
  (thousand-theorems__rocq__Q3527250), "Hadamard three-lines theorem":
  a bounded complex-differentiable function on a vertical strip is bounded
  by the logarithmic interpolation of its boundary-line norm suprema.
  This file contains no proof.
*)

From Stdlib Require Import Reals ClassicalEpsilon.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q3527250_complex : Type := (R * R)%type.

Definition q3527250_czero : q3527250_complex := (0, 0).
Definition q3527250_cone : q3527250_complex := (1, 0).

Definition q3527250_cadd
    (z w : q3527250_complex) : q3527250_complex :=
  (fst z + fst w, snd z + snd w).

Definition q3527250_cneg
    (z : q3527250_complex) : q3527250_complex :=
  (- fst z, - snd z).

Definition q3527250_csub
    (z w : q3527250_complex) : q3527250_complex :=
  q3527250_cadd z (q3527250_cneg w).

Definition q3527250_cmul
    (z w : q3527250_complex) : q3527250_complex :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition q3527250_cmodulus
    (z : q3527250_complex) : R :=
  sqrt (fst z * fst z + snd z * snd z).

Definition q3527250_vertical_strip
    (l u : R) (z : q3527250_complex) : Prop :=
  l < fst z /\ fst z < u.

Definition q3527250_vertical_closed_strip
    (l u : R) (z : q3527250_complex) : Prop :=
  l <= fst z /\ fst z <= u.

Record q3527250_normed_complex_vector_space (E : Type) : Type := {
  q3527250_zero : E;
  q3527250_add : E -> E -> E;
  q3527250_neg : E -> E;
  q3527250_smul : q3527250_complex -> E -> E;
  q3527250_norm : E -> R;

  q3527250_add_assoc :
    forall x y z : E,
      q3527250_add x (q3527250_add y z) =
      q3527250_add (q3527250_add x y) z;
  q3527250_add_comm :
    forall x y : E, q3527250_add x y = q3527250_add y x;
  q3527250_add_zero :
    forall x : E, q3527250_add x q3527250_zero = x;
  q3527250_add_neg :
    forall x : E,
      q3527250_add x (q3527250_neg x) = q3527250_zero;

  q3527250_one_smul :
    forall x : E, q3527250_smul q3527250_cone x = x;
  q3527250_mul_smul :
    forall (a b : q3527250_complex) (x : E),
      q3527250_smul (q3527250_cmul a b) x =
      q3527250_smul a (q3527250_smul b x);
  q3527250_add_smul :
    forall (a b : q3527250_complex) (x : E),
      q3527250_smul (q3527250_cadd a b) x =
      q3527250_add
        (q3527250_smul a x) (q3527250_smul b x);
  q3527250_smul_add :
    forall (a : q3527250_complex) (x y : E),
      q3527250_smul a (q3527250_add x y) =
      q3527250_add
        (q3527250_smul a x) (q3527250_smul a y);
  q3527250_zero_smul :
    forall x : E,
      q3527250_smul q3527250_czero x = q3527250_zero;
  q3527250_smul_zero :
    forall a : q3527250_complex,
      q3527250_smul a q3527250_zero = q3527250_zero;

  q3527250_norm_nonnegative :
    forall x : E, 0 <= q3527250_norm x;
  q3527250_norm_eq_zero :
    forall x : E,
      q3527250_norm x = 0 <-> x = q3527250_zero;
  q3527250_norm_add_le :
    forall x y : E,
      q3527250_norm (q3527250_add x y) <=
      q3527250_norm x + q3527250_norm y;
  q3527250_norm_smul :
    forall (a : q3527250_complex) (x : E),
      q3527250_norm (q3527250_smul a x) =
      q3527250_cmodulus a * q3527250_norm x
}.

Arguments q3527250_zero {E} _.
Arguments q3527250_add {E} _ _ _.
Arguments q3527250_neg {E} _ _.
Arguments q3527250_smul {E} _ _ _.
Arguments q3527250_norm {E} _ _.

Definition q3527250_sub
    {E : Type}
    (V : q3527250_normed_complex_vector_space E)
    (x y : E) : E :=
  q3527250_add V x (q3527250_neg V y).

Record q3527250_complex_linear_map
    {E : Type}
    (V : q3527250_normed_complex_vector_space E) : Type := {
  q3527250_linear_apply : q3527250_complex -> E;
  q3527250_linear_add :
    forall z w : q3527250_complex,
      q3527250_linear_apply (q3527250_cadd z w) =
      q3527250_add V
        (q3527250_linear_apply z) (q3527250_linear_apply w);
  q3527250_linear_smul :
    forall z w : q3527250_complex,
      q3527250_linear_apply (q3527250_cmul z w) =
      q3527250_smul V z (q3527250_linear_apply w);
  q3527250_linear_bounded :
    exists bound : R,
      0 <= bound /\
      forall z : q3527250_complex,
        q3527250_norm V (q3527250_linear_apply z) <=
        bound * q3527250_cmodulus z
}.

Arguments q3527250_linear_apply {E V} _ _.

Definition q3527250_continuous_within_at
    {E : Type}
    (V : q3527250_normed_complex_vector_space E)
    (f : q3527250_complex -> E)
    (S : q3527250_complex -> Prop)
    (z : q3527250_complex) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall w : q3527250_complex,
        S w ->
        q3527250_cmodulus (q3527250_csub w z) < delta ->
        q3527250_norm V (q3527250_sub V (f w) (f z)) < epsilon.

Definition q3527250_continuous_on
    {E : Type}
    (V : q3527250_normed_complex_vector_space E)
    (f : q3527250_complex -> E)
    (S : q3527250_complex -> Prop) : Prop :=
  forall z : q3527250_complex,
    S z -> q3527250_continuous_within_at V f S z.

Definition q3527250_has_frechet_deriv_within_at
    {E : Type}
    (V : q3527250_normed_complex_vector_space E)
    (f : q3527250_complex -> E)
    (S : q3527250_complex -> Prop)
    (z : q3527250_complex)
    (D : q3527250_complex_linear_map V) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall w : q3527250_complex,
        S w ->
        q3527250_cmodulus (q3527250_csub w z) < delta ->
        q3527250_norm V
          (q3527250_sub V
            (q3527250_sub V (f w) (f z))
            (q3527250_linear_apply D (q3527250_csub w z))) <=
        epsilon * q3527250_cmodulus (q3527250_csub w z).

Definition q3527250_differentiable_on
    {E : Type}
    (V : q3527250_normed_complex_vector_space E)
    (f : q3527250_complex -> E)
    (S : q3527250_complex -> Prop) : Prop :=
  forall z : q3527250_complex,
    S z ->
    exists D : q3527250_complex_linear_map V,
      @q3527250_has_frechet_deriv_within_at E V f S z D.

Definition q3527250_diff_cont_on_closed_strip
    {E : Type}
    (V : q3527250_normed_complex_vector_space E)
    (f : q3527250_complex -> E)
    (l u : R) : Prop :=
  q3527250_differentiable_on V f
    (q3527250_vertical_strip l u) /\
  q3527250_continuous_on V f
    (q3527250_vertical_closed_strip l u).

Definition q3527250_bounded_on_closed_strip
    {E : Type}
    (V : q3527250_normed_complex_vector_space E)
    (f : q3527250_complex -> E)
    (l u : R) : Prop :=
  exists bound : R,
    forall z : q3527250_complex,
      q3527250_vertical_closed_strip l u z ->
      q3527250_norm V (f z) <= bound.

Definition q3527250_is_boundary_norm_supremum
    {E : Type}
    (V : q3527250_normed_complex_vector_space E)
    (f : q3527250_complex -> E)
    (x supremum : R) : Prop :=
  (forall z : q3527250_complex,
      fst z = x ->
      q3527250_norm V (f z) <= supremum) /\
  forall upper : R,
    (forall z : q3527250_complex,
      fst z = x ->
      q3527250_norm V (f z) <= upper) ->
    supremum <= upper.

Definition q3527250_sSupNormIm
    {E : Type}
    (V : q3527250_normed_complex_vector_space E)
    (f : q3527250_complex -> E)
    (x : R) : R :=
  epsilon (inhabits 0)
    (fun supremum : R =>
      q3527250_is_boundary_norm_supremum V f x supremum).

Definition q3527250_interp_strip_norm
    {E : Type}
    (V : q3527250_normed_complex_vector_space E)
    (f : q3527250_complex -> E)
    (l u : R)
    (z : q3527250_complex) : R :=
  let left := q3527250_sSupNormIm V f l in
  let right := q3527250_sSupNormIm V f u in
  let t := (fst z - l) / (u - l) in
  if Req_EM_T left 0 then 0
  else if Req_EM_T right 0 then 0
  else
    exp (ln left * (1 - t)) *
    exp (ln right * t).

Theorem Complex_HadamardThreeLines_norm_le_interpStrip_of_mem_verticalClosedStrip :
  forall (E : Type)
         (V : q3527250_normed_complex_vector_space E)
         (l u : R)
         (f : q3527250_complex -> E)
         (z : q3527250_complex),
    l < u ->
    q3527250_vertical_closed_strip l u z ->
    q3527250_diff_cont_on_closed_strip V f l u ->
    q3527250_bounded_on_closed_strip V f l u ->
    q3527250_norm V (f z) <=
      q3527250_interp_strip_norm V f l u z.
Admitted.
