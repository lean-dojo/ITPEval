(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2093886
  (thousand-theorems__rocq__Q2093886), "Primitive element theorem": every
  finite-dimensional separable field extension is generated over its base
  field by a single element. This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Import ListNotations.

Record q2093886_field (K : Type) : Type := {
  q2093886_zero : K;
  q2093886_one : K;
  q2093886_add : K -> K -> K;
  q2093886_mul : K -> K -> K;
  q2093886_neg : K -> K;
  q2093886_inv : K -> K;
  q2093886_add_assoc :
    forall x y z : K,
      q2093886_add x (q2093886_add y z) =
      q2093886_add (q2093886_add x y) z;
  q2093886_add_comm :
    forall x y : K, q2093886_add x y = q2093886_add y x;
  q2093886_add_zero :
    forall x : K, q2093886_add x q2093886_zero = x;
  q2093886_add_neg :
    forall x : K, q2093886_add x (q2093886_neg x) = q2093886_zero;
  q2093886_mul_assoc :
    forall x y z : K,
      q2093886_mul x (q2093886_mul y z) =
      q2093886_mul (q2093886_mul x y) z;
  q2093886_mul_comm :
    forall x y : K, q2093886_mul x y = q2093886_mul y x;
  q2093886_mul_one :
    forall x : K, q2093886_mul x q2093886_one = x;
  q2093886_left_distrib :
    forall x y z : K,
      q2093886_mul x (q2093886_add y z) =
      q2093886_add
        (q2093886_mul x y) (q2093886_mul x z);
  q2093886_inv_zero :
    q2093886_inv q2093886_zero = q2093886_zero;
  q2093886_mul_inv :
    forall x : K,
      x <> q2093886_zero ->
      q2093886_mul x (q2093886_inv x) = q2093886_one;
  q2093886_nontrivial : q2093886_zero <> q2093886_one
}.

Arguments q2093886_zero {K} _.
Arguments q2093886_one {K} _.
Arguments q2093886_add {K} _ _ _.
Arguments q2093886_mul {K} _ _ _.
Arguments q2093886_neg {K} _ _.
Arguments q2093886_inv {K} _ _.

Record q2093886_field_algebra
    (F E : Type)
    (FF : q2093886_field F)
    (FE : q2093886_field E) : Type := {
  q2093886_embed : F -> E;
  q2093886_embed_zero :
    q2093886_embed (q2093886_zero FF) = q2093886_zero FE;
  q2093886_embed_one :
    q2093886_embed (q2093886_one FF) = q2093886_one FE;
  q2093886_embed_add :
    forall a b : F,
      q2093886_embed (q2093886_add FF a b) =
      q2093886_add FE (q2093886_embed a) (q2093886_embed b);
  q2093886_embed_mul :
    forall a b : F,
      q2093886_embed (q2093886_mul FF a b) =
      q2093886_mul FE (q2093886_embed a) (q2093886_embed b);
  q2093886_embed_injective :
    forall a b : F,
      q2093886_embed a = q2093886_embed b -> a = b
}.

Arguments q2093886_embed {F E FF FE} _ _.

Fixpoint q2093886_nat_mul
    {K : Type}
    (FK : q2093886_field K)
    (n : nat) (x : K) : K :=
  match n with
  | O => q2093886_zero FK
  | S m => q2093886_add FK x (q2093886_nat_mul FK m x)
  end.

Definition q2093886_polynomial (K : Type) : Type := list K.

Definition q2093886_polynomial_zero
    {K : Type} : q2093886_polynomial K :=
  [].

Definition q2093886_polynomial_one
    {K : Type}
    (FK : q2093886_field K) : q2093886_polynomial K :=
  [q2093886_one FK].

Fixpoint q2093886_polynomial_add
    {K : Type}
    (FK : q2093886_field K)
    (p q : q2093886_polynomial K) : q2093886_polynomial K :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: p', b :: q' =>
      q2093886_add FK a b ::
      q2093886_polynomial_add FK p' q'
  end.

Fixpoint q2093886_polynomial_mul
    {K : Type}
    (FK : q2093886_field K)
    (p q : q2093886_polynomial K) : q2093886_polynomial K :=
  match p with
  | [] => []
  | a :: p' =>
      q2093886_polynomial_add FK
        (map (fun b => q2093886_mul FK a b) q)
        (q2093886_zero FK ::
          q2093886_polynomial_mul FK p' q)
  end.

Fixpoint q2093886_polynomial_derivative_aux
    {K : Type}
    (FK : q2093886_field K)
    (degree : nat)
    (p : q2093886_polynomial K) : q2093886_polynomial K :=
  match p with
  | [] => []
  | coefficient :: rest =>
      q2093886_nat_mul FK degree coefficient ::
      q2093886_polynomial_derivative_aux FK (S degree) rest
  end.

Definition q2093886_polynomial_derivative
    {K : Type}
    (FK : q2093886_field K)
    (p : q2093886_polynomial K) : q2093886_polynomial K :=
  match p with
  | [] => []
  | _ :: rest =>
      q2093886_polynomial_derivative_aux FK 1 rest
  end.

Definition q2093886_polynomial_equiv
    {K : Type}
    (FK : q2093886_field K)
    (p q : q2093886_polynomial K) : Prop :=
  forall n : nat,
    nth n p (q2093886_zero FK) =
    nth n q (q2093886_zero FK).

Definition q2093886_polynomial_nonzero
    {K : Type}
    (FK : q2093886_field K)
    (p : q2093886_polynomial K) : Prop :=
  exists n : nat,
    nth n p (q2093886_zero FK) <> q2093886_zero FK.

Definition q2093886_polynomial_separable
    {K : Type}
    (FK : q2093886_field K)
    (p : q2093886_polynomial K) : Prop :=
  exists a b : q2093886_polynomial K,
    q2093886_polynomial_equiv FK
      (q2093886_polynomial_add FK
        (q2093886_polynomial_mul FK a p)
        (q2093886_polynomial_mul FK b
          (q2093886_polynomial_derivative FK p)))
      (q2093886_polynomial_one FK).

Fixpoint q2093886_polynomial_eval
    {F E : Type}
    {FF : q2093886_field F}
    {FE : q2093886_field E}
    (A : @q2093886_field_algebra F E FF FE)
    (p : q2093886_polynomial F)
    (x : E) : E :=
  match p with
  | [] => q2093886_zero FE
  | coefficient :: rest =>
      q2093886_add FE
        (q2093886_embed A coefficient)
        (q2093886_mul FE x
          (q2093886_polynomial_eval A rest x))
  end.

Fixpoint q2093886_linear_combination
    {F E : Type}
    {FF : q2093886_field F}
    {FE : q2093886_field E}
    (A : @q2093886_field_algebra F E FF FE)
    (coefficients : list F)
    (vectors : list E) : E :=
  match coefficients, vectors with
  | a :: coefficients', x :: vectors' =>
      q2093886_add FE
        (q2093886_mul FE (q2093886_embed A a) x)
        (q2093886_linear_combination A coefficients' vectors')
  | _, _ => q2093886_zero FE
  end.

Definition q2093886_finite_dimensional
    {F E : Type}
    {FF : q2093886_field F}
    {FE : q2093886_field E}
    (A : @q2093886_field_algebra F E FF FE) : Prop :=
  exists spanning_family : list E,
    forall x : E,
      exists coefficients : list F,
        length coefficients = length spanning_family /\
        q2093886_linear_combination A coefficients spanning_family = x.

Definition q2093886_is_separable
    {F E : Type}
    {FF : q2093886_field F}
    {FE : q2093886_field E}
    (A : @q2093886_field_algebra F E FF FE) : Prop :=
  forall x : E,
    exists p : q2093886_polynomial F,
      q2093886_polynomial_nonzero FF p /\
      q2093886_polynomial_separable FF p /\
      q2093886_polynomial_eval A p x = q2093886_zero FE.

Inductive q2093886_generated
    {F E : Type}
    {FF : q2093886_field F}
    {FE : q2093886_field E}
    (A : @q2093886_field_algebra F E FF FE)
    (alpha : E) : E -> Prop :=
  | q2093886_generated_base :
      forall a : F,
        q2093886_generated A alpha (q2093886_embed A a)
  | q2093886_generated_element :
      q2093886_generated A alpha alpha
  | q2093886_generated_add :
      forall x y : E,
        q2093886_generated A alpha x ->
        q2093886_generated A alpha y ->
        q2093886_generated A alpha (q2093886_add FE x y)
  | q2093886_generated_mul :
      forall x y : E,
        q2093886_generated A alpha x ->
        q2093886_generated A alpha y ->
        q2093886_generated A alpha (q2093886_mul FE x y)
  | q2093886_generated_neg :
      forall x : E,
        q2093886_generated A alpha x ->
        q2093886_generated A alpha (q2093886_neg FE x)
  | q2093886_generated_inv :
      forall x : E,
        q2093886_generated A alpha x ->
        q2093886_generated A alpha (q2093886_inv FE x).

Definition q2093886_generates_extension
    {F E : Type}
    {FF : q2093886_field F}
    {FE : q2093886_field E}
    (A : @q2093886_field_algebra F E FF FE)
    (alpha : E) : Prop :=
  forall x : E, q2093886_generated A alpha x.

Theorem Field_exists_primitive_element :
  forall (F E : Type)
         (FF : q2093886_field F)
         (FE : q2093886_field E)
         (A : @q2093886_field_algebra F E FF FE),
    q2093886_finite_dimensional A ->
    q2093886_is_separable A ->
    exists alpha : E,
      q2093886_generates_extension A alpha.
Admitted.
