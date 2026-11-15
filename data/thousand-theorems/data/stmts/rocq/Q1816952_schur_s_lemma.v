(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1816952
  (thousand-theorems__rocq__Q1816952), "Schur's lemma": over an algebraically
  closed field, the finite-dimensional endomorphism space of a simple object
  in a linear preadditive category with kernels has dimension one. This file
  contains no proof.
*)

From Stdlib Require Import List Vectors.Fin.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.

Record q1816952_field (K : Type) : Type := {
  q1816952_zero : K;
  q1816952_one : K;
  q1816952_add : K -> K -> K;
  q1816952_mul : K -> K -> K;
  q1816952_neg : K -> K;
  q1816952_inv : K -> K;
  q1816952_add_assoc :
    forall x y z : K,
      q1816952_add x (q1816952_add y z) =
      q1816952_add (q1816952_add x y) z;
  q1816952_add_comm :
    forall x y : K, q1816952_add x y = q1816952_add y x;
  q1816952_add_zero :
    forall x : K, q1816952_add x q1816952_zero = x;
  q1816952_add_neg :
    forall x : K, q1816952_add x (q1816952_neg x) = q1816952_zero;
  q1816952_mul_assoc :
    forall x y z : K,
      q1816952_mul x (q1816952_mul y z) =
      q1816952_mul (q1816952_mul x y) z;
  q1816952_mul_comm :
    forall x y : K, q1816952_mul x y = q1816952_mul y x;
  q1816952_mul_one :
    forall x : K, q1816952_mul x q1816952_one = x;
  q1816952_left_distrib :
    forall x y z : K,
      q1816952_mul x (q1816952_add y z) =
      q1816952_add
        (q1816952_mul x y) (q1816952_mul x z);
  q1816952_mul_inv :
    forall x : K, x <> q1816952_zero ->
      q1816952_mul x (q1816952_inv x) = q1816952_one;
  q1816952_nontrivial : q1816952_zero <> q1816952_one
}.

Arguments q1816952_zero {K} _.
Arguments q1816952_one {K} _.
Arguments q1816952_add {K} _ _ _.
Arguments q1816952_mul {K} _ _ _.
Arguments q1816952_neg {K} _ _.
Arguments q1816952_inv {K} _ _.

Fixpoint q1816952_polynomial_eval
    {K : Type} (F : q1816952_field K)
    (coefficients : list K) (x : K) : K :=
  match coefficients with
  | nil => q1816952_zero F
  | cons c rest =>
      q1816952_add F c
        (q1816952_mul F x
          (q1816952_polynomial_eval F rest x))
  end.

Fixpoint q1816952_some_nonzero
    {K : Type} (F : q1816952_field K)
    (coefficients : list K) : Prop :=
  match coefficients with
  | nil => False
  | cons c rest =>
      c <> q1816952_zero F \/
      q1816952_some_nonzero F rest
  end.

Definition q1816952_polynomial_nonconstant
    {K : Type} (F : q1816952_field K)
    (coefficients : list K) : Prop :=
  match coefficients with
  | nil => False
  | cons _ positive_degree_coefficients =>
      q1816952_some_nonzero F positive_degree_coefficients
  end.

Definition q1816952_is_algebraically_closed
    {K : Type} (F : q1816952_field K) : Prop :=
  forall coefficients : list K,
    q1816952_polynomial_nonconstant F coefficients ->
    exists x : K,
      q1816952_polynomial_eval F coefficients x =
      q1816952_zero F.

Record q1816952_category : Type := {
  q1816952_obj : Type;
  q1816952_hom : q1816952_obj -> q1816952_obj -> Type;
  q1816952_id :
    forall X : q1816952_obj, q1816952_hom X X;
  q1816952_comp :
    forall X Y Z : q1816952_obj,
      q1816952_hom X Y ->
      q1816952_hom Y Z ->
      q1816952_hom X Z;
  q1816952_comp_id_left :
    forall (X Y : q1816952_obj) (f : q1816952_hom X Y),
      @q1816952_comp X X Y (q1816952_id X) f = f;
  q1816952_comp_id_right :
    forall (X Y : q1816952_obj) (f : q1816952_hom X Y),
      @q1816952_comp X Y Y f (q1816952_id Y) = f;
  q1816952_comp_assoc :
    forall (W X Y Z : q1816952_obj)
           (f : q1816952_hom W X)
           (g : q1816952_hom X Y)
           (h : q1816952_hom Y Z),
      @q1816952_comp W Y Z (@q1816952_comp W X Y f g) h =
      @q1816952_comp W X Z f (@q1816952_comp X Y Z g h)
}.

Arguments q1816952_obj _ : clear implicits.
Arguments q1816952_hom _ _ _ : clear implicits.
Arguments q1816952_id {q} _.
Arguments q1816952_comp {q} {X Y Z} _ _.

Record q1816952_abelian_group (A : Type) : Type := {
  q1816952_ag_zero : A;
  q1816952_ag_add : A -> A -> A;
  q1816952_ag_neg : A -> A;
  q1816952_ag_add_assoc :
    forall x y z : A,
      q1816952_ag_add x (q1816952_ag_add y z) =
      q1816952_ag_add (q1816952_ag_add x y) z;
  q1816952_ag_add_comm :
    forall x y : A, q1816952_ag_add x y = q1816952_ag_add y x;
  q1816952_ag_add_zero :
    forall x : A, q1816952_ag_add x q1816952_ag_zero = x;
  q1816952_ag_add_neg :
    forall x : A,
      q1816952_ag_add x (q1816952_ag_neg x) = q1816952_ag_zero
}.

Arguments q1816952_ag_zero {A} _.
Arguments q1816952_ag_add {A} _ _ _.
Arguments q1816952_ag_neg {A} _ _.

Record q1816952_preadditive (C : q1816952_category) : Type := {
  q1816952_hom_group :
    forall X Y : q1816952_obj C,
      q1816952_abelian_group (q1816952_hom C X Y);
  q1816952_comp_add_left :
    forall (W X Y : q1816952_obj C)
           (f g : q1816952_hom C W X)
           (h : q1816952_hom C X Y),
      q1816952_comp
        (q1816952_ag_add (q1816952_hom_group W X) f g) h =
      q1816952_ag_add (q1816952_hom_group W Y)
        (q1816952_comp f h) (q1816952_comp g h);
  q1816952_comp_add_right :
    forall (W X Y : q1816952_obj C)
           (f : q1816952_hom C W X)
           (g h : q1816952_hom C X Y),
      q1816952_comp f
        (q1816952_ag_add (q1816952_hom_group X Y) g h) =
      q1816952_ag_add (q1816952_hom_group W Y)
        (q1816952_comp f g) (q1816952_comp f h)
}.

Arguments q1816952_hom_group {C} _ _ _.

Definition q1816952_zero_morphism
    {C : q1816952_category}
    (P : q1816952_preadditive C)
    (X Y : q1816952_obj C) : q1816952_hom C X Y :=
  q1816952_ag_zero (q1816952_hom_group P X Y).

Record q1816952_linear
    {K : Type}
    (F : q1816952_field K)
    (C : q1816952_category)
    (P : q1816952_preadditive C) : Type := {
  q1816952_smul :
    forall X Y : q1816952_obj C,
      K -> q1816952_hom C X Y -> q1816952_hom C X Y;
  q1816952_one_smul :
    forall (X Y : q1816952_obj C) (f : q1816952_hom C X Y),
      q1816952_smul X Y (q1816952_one F) f = f;
  q1816952_mul_smul :
    forall (X Y : q1816952_obj C) (a b : K)
           (f : q1816952_hom C X Y),
      q1816952_smul X Y (q1816952_mul F a b) f =
      q1816952_smul X Y a (q1816952_smul X Y b f);
  q1816952_add_smul :
    forall (X Y : q1816952_obj C) (a b : K)
           (f : q1816952_hom C X Y),
      q1816952_smul X Y (q1816952_add F a b) f =
      q1816952_ag_add (q1816952_hom_group P X Y)
        (q1816952_smul X Y a f) (q1816952_smul X Y b f);
  q1816952_smul_add :
    forall (X Y : q1816952_obj C) (a : K)
           (f g : q1816952_hom C X Y),
      q1816952_smul X Y a
        (q1816952_ag_add (q1816952_hom_group P X Y) f g) =
      q1816952_ag_add (q1816952_hom_group P X Y)
        (q1816952_smul X Y a f) (q1816952_smul X Y a g);
  q1816952_zero_smul :
    forall (X Y : q1816952_obj C) (f : q1816952_hom C X Y),
      q1816952_smul X Y (q1816952_zero F) f =
      q1816952_zero_morphism P X Y;
  q1816952_smul_zero :
    forall (X Y : q1816952_obj C) (a : K),
      q1816952_smul X Y a (q1816952_zero_morphism P X Y) =
      q1816952_zero_morphism P X Y;
  q1816952_smul_comp :
    forall (X Y Z : q1816952_obj C) (a : K)
           (f : q1816952_hom C X Y)
           (g : q1816952_hom C Y Z),
      q1816952_comp (q1816952_smul X Y a f) g =
      q1816952_smul X Z a (q1816952_comp f g);
  q1816952_comp_smul :
    forall (X Y Z : q1816952_obj C) (a : K)
           (f : q1816952_hom C X Y)
           (g : q1816952_hom C Y Z),
      q1816952_comp f (q1816952_smul Y Z a g) =
      q1816952_smul X Z a (q1816952_comp f g)
}.

Arguments q1816952_smul {K F C P} _ {X Y} _ _.

Definition q1816952_is_isomorphism
    {C : q1816952_category}
    {X Y : q1816952_obj C}
    (f : q1816952_hom C X Y) : Prop :=
  exists g : q1816952_hom C Y X,
    q1816952_comp f g = q1816952_id X /\
    q1816952_comp g f = q1816952_id Y.

Definition q1816952_is_monomorphism
    {C : q1816952_category}
    {X Y : q1816952_obj C}
    (f : q1816952_hom C X Y) : Prop :=
  forall (Z : q1816952_obj C)
         (g h : q1816952_hom C Z X),
    q1816952_comp g f = q1816952_comp h f -> g = h.

Definition q1816952_simple
    {C : q1816952_category}
    (P : q1816952_preadditive C)
    (X : q1816952_obj C) : Prop :=
  forall (Y : q1816952_obj C)
         (f : q1816952_hom C Y X),
    q1816952_is_monomorphism f ->
    (q1816952_is_isomorphism f <->
     f <> q1816952_zero_morphism P Y X).

Definition q1816952_is_kernel
    {C : q1816952_category}
    (P : q1816952_preadditive C)
    {X Y Kernel : q1816952_obj C}
    (f : q1816952_hom C X Y)
    (kernel_arrow : q1816952_hom C Kernel X) : Prop :=
  q1816952_comp kernel_arrow f =
    q1816952_zero_morphism P Kernel Y /\
  forall (T : q1816952_obj C)
         (t : q1816952_hom C T X),
    q1816952_comp t f = q1816952_zero_morphism P T Y ->
    exists u : q1816952_hom C T Kernel,
      q1816952_comp u kernel_arrow = t /\
      forall v : q1816952_hom C T Kernel,
        q1816952_comp v kernel_arrow = t -> v = u.

Definition q1816952_has_kernels
    {C : q1816952_category}
    (P : q1816952_preadditive C) : Prop :=
  forall (X Y : q1816952_obj C)
         (f : q1816952_hom C X Y),
    exists Kernel : q1816952_obj C,
    exists kernel_arrow : q1816952_hom C Kernel X,
      q1816952_is_kernel P f kernel_arrow.

Fixpoint q1816952_endomorphism_sum
    {C : q1816952_category}
    (P : q1816952_preadditive C)
    (X : q1816952_obj C)
    (n : nat) : (Fin.t n -> q1816952_hom C X X) ->
                q1816952_hom C X X :=
  match n as m
        return (Fin.t m -> q1816952_hom C X X) ->
               q1816952_hom C X X with
  | O => fun _ => q1816952_zero_morphism P X X
  | S m =>
      fun terms =>
        q1816952_ag_add (q1816952_hom_group P X X)
          (terms Fin.F1)
          (@q1816952_endomorphism_sum C P X m
            (fun i => terms (Fin.FS i)))
  end.

Definition q1816952_is_basis
    {K : Type}
    {F : q1816952_field K}
    {C : q1816952_category}
    {P : q1816952_preadditive C}
    (L : @q1816952_linear K F C P)
    (X : q1816952_obj C)
    (n : nat)
    (basis : Fin.t n -> q1816952_hom C X X) : Prop :=
  (forall f : q1816952_hom C X X,
    exists coefficients : Fin.t n -> K,
      f =
      @q1816952_endomorphism_sum C P X n
        (fun i => q1816952_smul L (coefficients i) (basis i))) /\
  (forall coefficients : Fin.t n -> K,
    @q1816952_endomorphism_sum C P X n
      (fun i => q1816952_smul L (coefficients i) (basis i)) =
    q1816952_zero_morphism P X X ->
    forall i : Fin.t n, coefficients i = q1816952_zero F).

Definition q1816952_finite_dimensional_endomorphisms
    {K : Type}
    {F : q1816952_field K}
    {C : q1816952_category}
    {P : q1816952_preadditive C}
    (L : @q1816952_linear K F C P)
    (X : q1816952_obj C) : Prop :=
  exists n : nat,
  exists basis : Fin.t n -> q1816952_hom C X X,
    @q1816952_is_basis K F C P L X n basis.

Definition q1816952_endomorphism_dimension_one
    {K : Type}
    {F : q1816952_field K}
    {C : q1816952_category}
    {P : q1816952_preadditive C}
    (L : @q1816952_linear K F C P)
    (X : q1816952_obj C) : Prop :=
  exists basis : Fin.t 1 -> q1816952_hom C X X,
    @q1816952_is_basis K F C P L X 1 basis.

Theorem CategoryTheory_finrank_endomorphism_simple_eq_one :
  forall (K : Type)
         (F : q1816952_field K)
         (C : q1816952_category)
         (P : q1816952_preadditive C)
         (L : @q1816952_linear K F C P)
         (X : q1816952_obj C),
    q1816952_is_algebraically_closed F ->
    q1816952_has_kernels P ->
    q1816952_simple P X ->
    q1816952_finite_dimensional_endomorphisms L X ->
    q1816952_endomorphism_dimension_one L X.
Admitted.
