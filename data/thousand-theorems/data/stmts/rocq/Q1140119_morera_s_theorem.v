(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1140119
  (thousand-theorems__rocq__Q1140119), "Morera's theorem": for a function
  from the complex plane to an arbitrary complex Banach space on an open set,
  being conservative on rectangles and continuous is equivalent to being
  complex differentiable there. This file contains no proof.
*)

From Stdlib Require Import Reals Arith ClassicalEpsilon.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1140119_complex : Type := (R * R)%type.
Definition q1140119_set (A : Type) : Type := A -> Prop.

Definition q1140119_czero : q1140119_complex := (0, 0).
Definition q1140119_cone : q1140119_complex := (1, 0).
Definition q1140119_ci : q1140119_complex := (0, 1).

Definition q1140119_cadd
    (z w : q1140119_complex) : q1140119_complex :=
  (fst z + fst w, snd z + snd w).

Definition q1140119_cneg
    (z : q1140119_complex) : q1140119_complex :=
  (- fst z, - snd z).

Definition q1140119_csub
    (z w : q1140119_complex) : q1140119_complex :=
  q1140119_cadd z (q1140119_cneg w).

Definition q1140119_cmul
    (z w : q1140119_complex) : q1140119_complex :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition q1140119_of_real (x : R) : q1140119_complex :=
  (x, 0).

Definition q1140119_cmodulus
    (z : q1140119_complex) : R :=
  sqrt (fst z * fst z + snd z * snd z).

Record q1140119_normed_complex_vector_space (E : Type) : Type := {
  q1140119_zero : E;
  q1140119_add : E -> E -> E;
  q1140119_neg : E -> E;
  q1140119_smul : q1140119_complex -> E -> E;
  q1140119_norm : E -> R;

  q1140119_add_assoc :
    forall x y z : E,
      q1140119_add x (q1140119_add y z) =
      q1140119_add (q1140119_add x y) z;
  q1140119_add_comm :
    forall x y : E, q1140119_add x y = q1140119_add y x;
  q1140119_add_zero :
    forall x : E, q1140119_add x q1140119_zero = x;
  q1140119_add_neg :
    forall x : E,
      q1140119_add x (q1140119_neg x) = q1140119_zero;

  q1140119_one_smul :
    forall x : E, q1140119_smul q1140119_cone x = x;
  q1140119_mul_smul :
    forall (a b : q1140119_complex) (x : E),
      q1140119_smul (q1140119_cmul a b) x =
      q1140119_smul a (q1140119_smul b x);
  q1140119_add_smul :
    forall (a b : q1140119_complex) (x : E),
      q1140119_smul (q1140119_cadd a b) x =
      q1140119_add
        (q1140119_smul a x) (q1140119_smul b x);
  q1140119_smul_add :
    forall (a : q1140119_complex) (x y : E),
      q1140119_smul a (q1140119_add x y) =
      q1140119_add
        (q1140119_smul a x) (q1140119_smul a y);
  q1140119_zero_smul :
    forall x : E, q1140119_smul q1140119_czero x = q1140119_zero;
  q1140119_smul_zero :
    forall a : q1140119_complex,
      q1140119_smul a q1140119_zero = q1140119_zero;

  q1140119_norm_nonnegative :
    forall x : E, 0 <= q1140119_norm x;
  q1140119_norm_eq_zero :
    forall x : E, q1140119_norm x = 0 <-> x = q1140119_zero;
  q1140119_norm_add_le :
    forall x y : E,
      q1140119_norm (q1140119_add x y) <=
      q1140119_norm x + q1140119_norm y;
  q1140119_norm_smul :
    forall (a : q1140119_complex) (x : E),
      q1140119_norm (q1140119_smul a x) =
      q1140119_cmodulus a * q1140119_norm x
}.

Arguments q1140119_zero {E} _.
Arguments q1140119_add {E} _ _ _.
Arguments q1140119_neg {E} _ _.
Arguments q1140119_smul {E} _ _ _.
Arguments q1140119_norm {E} _ _.

Definition q1140119_sub
    {E : Type}
    (V : q1140119_normed_complex_vector_space E)
    (x y : E) : E :=
  q1140119_add V x (q1140119_neg V y).

Definition q1140119_sequence_converges
    {E : Type}
    (V : q1140119_normed_complex_vector_space E)
    (u : nat -> E) (limit : E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q1140119_norm V
          (q1140119_sub V (u n) limit) < epsilon.

Definition q1140119_sequence_cauchy
    {E : Type}
    (V : q1140119_normed_complex_vector_space E)
    (u : nat -> E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q1140119_norm V
          (q1140119_sub V (u m) (u n)) < epsilon.

Definition q1140119_complete
    {E : Type}
    (V : q1140119_normed_complex_vector_space E) : Prop :=
  forall u : nat -> E,
    q1140119_sequence_cauchy V u ->
    exists limit : E,
      q1140119_sequence_converges V u limit.

Fixpoint q1140119_sum_first
    {E : Type}
    (V : q1140119_normed_complex_vector_space E)
    (term : nat -> E) (n : nat) : E :=
  match n with
  | O => q1140119_zero V
  | S k => q1140119_add V (q1140119_sum_first V term k) (term k)
  end.

Definition q1140119_uniform_riemann_sum
    {E : Type}
    (V : q1140119_normed_complex_vector_space E)
    (g : R -> E) (a b : R) (n : nat) : E :=
  let step := (b - a) / INR n in
  q1140119_sum_first V
    (fun k : nat =>
      q1140119_smul V (q1140119_of_real step)
        (g (a + INR k * step)))
    n.

Definition q1140119_forward_riemann_limit
    {E : Type}
    (V : q1140119_normed_complex_vector_space E)
    (g : R -> E) (a b : R) (value : E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        (0 < n)%nat ->
        q1140119_norm V
          (q1140119_sub V
            (q1140119_uniform_riemann_sum V g a b n)
            value) < epsilon.

Definition q1140119_interval_integral_value
    {E : Type}
    (V : q1140119_normed_complex_vector_space E)
    (g : R -> E) (a b : R) (value : E) : Prop :=
  if Rle_dec a b then
    q1140119_forward_riemann_limit V g a b value
  else
    q1140119_forward_riemann_limit V g b a
      (q1140119_neg V value).

Definition q1140119_interval_integral
    {E : Type}
    (V : q1140119_normed_complex_vector_space E)
    (g : R -> E) (a b : R) : E :=
  if excluded_middle_informative
      (exists value : E,
        q1140119_interval_integral_value V g a b value)
  then
    epsilon (inhabits (q1140119_zero V))
      (fun value : E =>
        q1140119_interval_integral_value V g a b value)
  else q1140119_zero V.

Definition q1140119_between (a b x : R) : Prop :=
  (a <= x /\ x <= b) \/ (b <= x /\ x <= a).

Definition q1140119_rectangle
    (z w : q1140119_complex) :
    q1140119_set q1140119_complex :=
  fun u =>
    q1140119_between (fst z) (fst w) (fst u) /\
    q1140119_between (snd z) (snd w) (snd u).

Definition q1140119_subset
    {A : Type}
    (S T : q1140119_set A) : Prop :=
  forall x : A, S x -> T x.

Definition q1140119_wedge_integral
    {E : Type}
    (V : q1140119_normed_complex_vector_space E)
    (z w : q1140119_complex)
    (f : q1140119_complex -> E) : E :=
  q1140119_add V
    (q1140119_interval_integral V
      (fun x : R => f (x, snd z)) (fst z) (fst w))
    (q1140119_smul V q1140119_ci
      (q1140119_interval_integral V
        (fun y : R => f (fst w, y)) (snd z) (snd w))).

Definition q1140119_is_conservative_on
    {E : Type}
    (V : q1140119_normed_complex_vector_space E)
    (f : q1140119_complex -> E)
    (U : q1140119_set q1140119_complex) : Prop :=
  forall z w : q1140119_complex,
    q1140119_subset (q1140119_rectangle z w) U ->
    q1140119_wedge_integral V z w f =
    q1140119_neg V (q1140119_wedge_integral V w z f).

Definition q1140119_is_open
    (U : q1140119_set q1140119_complex) : Prop :=
  forall z : q1140119_complex,
    U z ->
    exists delta : R,
      0 < delta /\
      forall w : q1140119_complex,
        q1140119_cmodulus (q1140119_csub w z) < delta ->
        U w.

Definition q1140119_continuous_within_at
    {E : Type}
    (V : q1140119_normed_complex_vector_space E)
    (f : q1140119_complex -> E)
    (U : q1140119_set q1140119_complex)
    (z : q1140119_complex) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall w : q1140119_complex,
        U w ->
        q1140119_cmodulus (q1140119_csub w z) < delta ->
        q1140119_norm V
          (q1140119_sub V (f w) (f z)) < epsilon.

Definition q1140119_continuous_on
    {E : Type}
    (V : q1140119_normed_complex_vector_space E)
    (f : q1140119_complex -> E)
    (U : q1140119_set q1140119_complex) : Prop :=
  forall z : q1140119_complex,
    U z ->
    q1140119_continuous_within_at V f U z.

Record q1140119_continuous_complex_linear_map
    (E : Type)
    (V : q1140119_normed_complex_vector_space E) : Type := {
  q1140119_linear_apply : q1140119_complex -> E;
  q1140119_linear_add :
    forall z w : q1140119_complex,
      q1140119_linear_apply (q1140119_cadd z w) =
      q1140119_add V
        (q1140119_linear_apply z) (q1140119_linear_apply w);
  q1140119_linear_smul :
    forall a z : q1140119_complex,
      q1140119_linear_apply (q1140119_cmul a z) =
      q1140119_smul V a (q1140119_linear_apply z);
  q1140119_linear_bounded :
    exists bound : R,
      0 <= bound /\
      forall z : q1140119_complex,
        q1140119_norm V (q1140119_linear_apply z) <=
        bound * q1140119_cmodulus z
}.

Arguments q1140119_linear_apply {E V} _ _.

Definition q1140119_has_frechet_derivative_within_at
    {E : Type}
    (V : q1140119_normed_complex_vector_space E)
    (f : q1140119_complex -> E)
    (U : q1140119_set q1140119_complex)
    (z : q1140119_complex)
    (D : q1140119_continuous_complex_linear_map V) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall w : q1140119_complex,
        U w ->
        q1140119_cmodulus (q1140119_csub w z) < delta ->
        q1140119_norm V
          (q1140119_sub V
            (q1140119_sub V (f w) (f z))
            (q1140119_linear_apply D
              (q1140119_csub w z))) <=
        epsilon * q1140119_cmodulus (q1140119_csub w z).

Definition q1140119_differentiable_on
    {E : Type}
    (V : q1140119_normed_complex_vector_space E)
    (f : q1140119_complex -> E)
    (U : q1140119_set q1140119_complex) : Prop :=
  forall z : q1140119_complex,
    U z ->
    exists D : q1140119_continuous_complex_linear_map V,
      @q1140119_has_frechet_derivative_within_at E V f U z D.

Theorem isConservativeOn_and_continuousOn_iff_isDifferentiableOn :
  forall (E : Type)
         (V : q1140119_normed_complex_vector_space E),
    q1140119_complete V ->
    forall (f : q1140119_complex -> E)
           (U : q1140119_set q1140119_complex),
      q1140119_is_open U ->
      (q1140119_is_conservative_on V f U /\
       q1140119_continuous_on V f U) <->
      q1140119_differentiable_on V f U.
Admitted.
