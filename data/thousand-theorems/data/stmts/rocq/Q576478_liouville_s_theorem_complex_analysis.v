(*
  Statement-only formalization of Thousand Theorems corpus artifact Q576478
  (thousand-theorems__rocq__Q576478), "Liouville's theorem (complex
  analysis)": an everywhere complex-differentiable map between complex normed
  vector spaces with bounded range takes the same value at every two points.
  This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q576478_complex : Type := (R * R)%type.

Definition q576478_czero : q576478_complex := (0, 0).
Definition q576478_cone : q576478_complex := (1, 0).

Definition q576478_cadd
    (z w : q576478_complex) : q576478_complex :=
  (fst z + fst w, snd z + snd w).

Definition q576478_cneg
    (z : q576478_complex) : q576478_complex :=
  (- fst z, - snd z).

Definition q576478_cmul
    (z w : q576478_complex) : q576478_complex :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition q576478_cmodulus
    (z : q576478_complex) : R :=
  sqrt (fst z * fst z + snd z * snd z).

Record q576478_normed_complex_vector_space (E : Type) : Type := {
  q576478_zero : E;
  q576478_add : E -> E -> E;
  q576478_neg : E -> E;
  q576478_smul : q576478_complex -> E -> E;
  q576478_norm : E -> R;

  q576478_add_assoc :
    forall x y z : E,
      q576478_add x (q576478_add y z) =
      q576478_add (q576478_add x y) z;
  q576478_add_comm :
    forall x y : E, q576478_add x y = q576478_add y x;
  q576478_add_zero :
    forall x : E, q576478_add x q576478_zero = x;
  q576478_add_neg :
    forall x : E, q576478_add x (q576478_neg x) = q576478_zero;

  q576478_one_smul :
    forall x : E, q576478_smul q576478_cone x = x;
  q576478_mul_smul :
    forall (a b : q576478_complex) (x : E),
      q576478_smul (q576478_cmul a b) x =
      q576478_smul a (q576478_smul b x);
  q576478_add_smul :
    forall (a b : q576478_complex) (x : E),
      q576478_smul (q576478_cadd a b) x =
      q576478_add (q576478_smul a x) (q576478_smul b x);
  q576478_smul_add :
    forall (a : q576478_complex) (x y : E),
      q576478_smul a (q576478_add x y) =
      q576478_add (q576478_smul a x) (q576478_smul a y);
  q576478_zero_smul :
    forall x : E, q576478_smul q576478_czero x = q576478_zero;
  q576478_smul_zero :
    forall a : q576478_complex,
      q576478_smul a q576478_zero = q576478_zero;

  q576478_norm_nonnegative :
    forall x : E, 0 <= q576478_norm x;
  q576478_norm_eq_zero :
    forall x : E, q576478_norm x = 0 <-> x = q576478_zero;
  q576478_norm_neg :
    forall x : E,
      q576478_norm (q576478_neg x) = q576478_norm x;
  q576478_norm_add_le :
    forall x y : E,
      q576478_norm (q576478_add x y) <=
      q576478_norm x + q576478_norm y;
  q576478_norm_smul :
    forall (a : q576478_complex) (x : E),
      q576478_norm (q576478_smul a x) =
      q576478_cmodulus a * q576478_norm x
}.

Arguments q576478_zero {E} _.
Arguments q576478_add {E} _ _ _.
Arguments q576478_neg {E} _ _.
Arguments q576478_smul {E} _ _ _.
Arguments q576478_norm {E} _ _.

Definition q576478_sub
    {E : Type}
    (V : q576478_normed_complex_vector_space E)
    (x y : E) : E :=
  q576478_add V x (q576478_neg V y).

Record q576478_continuous_complex_linear_map
    (E F : Type)
    (VE : q576478_normed_complex_vector_space E)
    (VF : q576478_normed_complex_vector_space F) : Type := {
  q576478_linear_apply : E -> F;
  q576478_linear_add :
    forall x y : E,
      q576478_linear_apply (q576478_add VE x y) =
      q576478_add VF
        (q576478_linear_apply x) (q576478_linear_apply y);
  q576478_linear_smul :
    forall (a : q576478_complex) (x : E),
      q576478_linear_apply (q576478_smul VE a x) =
      q576478_smul VF a (q576478_linear_apply x);
  q576478_linear_bounded :
    exists C : R,
      0 <= C /\
      forall x : E,
        q576478_norm VF (q576478_linear_apply x) <=
        C * q576478_norm VE x
}.

Arguments q576478_linear_apply {E F VE VF} _ _.

Definition q576478_has_frechet_derivative_at
    {E F : Type}
    (VE : q576478_normed_complex_vector_space E)
    (VF : q576478_normed_complex_vector_space F)
    (f : E -> F) (x : E)
    (D : @q576478_continuous_complex_linear_map E F VE VF) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall h : E,
        q576478_norm VE h < delta ->
        q576478_norm VF
          (q576478_sub VF
            (q576478_sub VF
              (f (q576478_add VE x h)) (f x))
            (q576478_linear_apply D h)) <=
        epsilon * q576478_norm VE h.

Definition q576478_differentiable
    {E F : Type}
    (VE : q576478_normed_complex_vector_space E)
    (VF : q576478_normed_complex_vector_space F)
    (f : E -> F) : Prop :=
  forall x : E,
    exists D : @q576478_continuous_complex_linear_map E F VE VF,
      @q576478_has_frechet_derivative_at E F VE VF f x D.

Definition q576478_bounded_range
    {E F : Type}
    (VF : q576478_normed_complex_vector_space F)
    (f : E -> F) : Prop :=
  exists C : R,
    0 <= C /\
    forall x : E, q576478_norm VF (f x) <= C.

Theorem Differentiable_apply_eq_apply_of_bounded :
  forall (E F : Type)
         (VE : q576478_normed_complex_vector_space E)
         (VF : q576478_normed_complex_vector_space F)
         (f : E -> F),
    q576478_differentiable VE VF f ->
    q576478_bounded_range VF f ->
    forall z w : E, f z = f w.
Admitted.
