(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1660147
  (thousand-theorems__rocq__Q1660147), "Mazur–Ulam theorem": every bijective
  isometry between real normed affine spaces is an affine isometry equivalence
  with the same underlying map. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q1660147_normed_real_vector_space (V : Type) : Type := {
  q1660147_zero : V;
  q1660147_add : V -> V -> V;
  q1660147_neg : V -> V;
  q1660147_smul : R -> V -> V;
  q1660147_norm : V -> R;

  q1660147_add_assoc :
    forall x y z : V,
      q1660147_add x (q1660147_add y z) =
      q1660147_add (q1660147_add x y) z;
  q1660147_add_comm :
    forall x y : V,
      q1660147_add x y = q1660147_add y x;
  q1660147_add_zero :
    forall x : V,
      q1660147_add x q1660147_zero = x;
  q1660147_add_neg :
    forall x : V,
      q1660147_add x (q1660147_neg x) = q1660147_zero;

  q1660147_one_smul :
    forall x : V,
      q1660147_smul 1 x = x;
  q1660147_mul_smul :
    forall (a b : R) (x : V),
      q1660147_smul (a * b) x =
      q1660147_smul a (q1660147_smul b x);
  q1660147_add_smul :
    forall (a b : R) (x : V),
      q1660147_smul (a + b) x =
      q1660147_add
        (q1660147_smul a x)
        (q1660147_smul b x);
  q1660147_smul_add :
    forall (a : R) (x y : V),
      q1660147_smul a (q1660147_add x y) =
      q1660147_add
        (q1660147_smul a x)
        (q1660147_smul a y);
  q1660147_zero_smul :
    forall x : V,
      q1660147_smul 0 x = q1660147_zero;
  q1660147_smul_zero :
    forall a : R,
      q1660147_smul a q1660147_zero = q1660147_zero;

  q1660147_norm_nonnegative :
    forall x : V,
      0 <= q1660147_norm x;
  q1660147_norm_eq_zero :
    forall x : V,
      q1660147_norm x = 0 <-> x = q1660147_zero;
  q1660147_norm_neg :
    forall x : V,
      q1660147_norm (q1660147_neg x) = q1660147_norm x;
  q1660147_norm_add_le :
    forall x y : V,
      q1660147_norm (q1660147_add x y) <=
      q1660147_norm x + q1660147_norm y;
  q1660147_norm_smul :
    forall (a : R) (x : V),
      q1660147_norm (q1660147_smul a x) =
      Rabs a * q1660147_norm x
}.

Arguments q1660147_zero {V} _.
Arguments q1660147_add {V} _ _ _.
Arguments q1660147_neg {V} _ _.
Arguments q1660147_smul {V} _ _ _.
Arguments q1660147_norm {V} _ _.

Record q1660147_normed_add_torsor
    (V P : Type)
    (S : q1660147_normed_real_vector_space V) : Type := {
  q1660147_basepoint : P;
  q1660147_vadd : V -> P -> P;
  q1660147_vsub : P -> P -> V;

  q1660147_zero_vadd :
    forall p : P,
      q1660147_vadd (q1660147_zero S) p = p;
  q1660147_add_vadd :
    forall (u v : V) (p : P),
      q1660147_vadd (q1660147_add S u v) p =
      q1660147_vadd u (q1660147_vadd v p);
  q1660147_vsub_vadd :
    forall p q : P,
      q1660147_vadd (q1660147_vsub p q) q = p;
  q1660147_vadd_vsub :
    forall (v : V) (p : P),
      q1660147_vsub (q1660147_vadd v p) p = v
}.

Arguments q1660147_vadd {V P S} _ _ _.
Arguments q1660147_vsub {V P S} _ _ _.

Definition q1660147_dist
    {V P : Type}
    {S : q1660147_normed_real_vector_space V}
    (T : @q1660147_normed_add_torsor V P S)
    (p q : P) : R :=
  q1660147_norm S (q1660147_vsub T p q).

Theorem IsometryEquiv_coe_toRealAffineIsometryEquiv :
  forall (E PE F PF : Type)
         (VE : q1660147_normed_real_vector_space E)
         (VF : q1660147_normed_real_vector_space F)
         (TE : @q1660147_normed_add_torsor E PE VE)
         (TF : @q1660147_normed_add_torsor F PF VF)
         (forward : PE -> PF)
         (inverse : PF -> PE),
    (forall p : PE, inverse (forward p) = p) ->
    (forall q : PF, forward (inverse q) = q) ->
    (forall p q : PE,
      q1660147_dist TF (forward p) (forward q) =
      q1660147_dist TE p q) ->
    exists (linear_part : E -> F)
           (linear_inverse : F -> E),
      (forall x y : E,
        linear_part (q1660147_add VE x y) =
        q1660147_add VF (linear_part x) (linear_part y)) /\
      (forall (a : R) (x : E),
        linear_part (q1660147_smul VE a x) =
        q1660147_smul VF a (linear_part x)) /\
      (forall x : E,
        q1660147_norm VF (linear_part x) =
        q1660147_norm VE x) /\
      (forall x : E,
        linear_inverse (linear_part x) = x) /\
      (forall y : F,
        linear_part (linear_inverse y) = y) /\
      (forall (v : E) (p : PE),
        forward (q1660147_vadd TE v p) =
        q1660147_vadd TF (linear_part v) (forward p)).
Admitted.
