(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527205
  (thousand-theorems__rocq__Q3527205), "Dimension theorem for vector spaces":
  over a semiring satisfying invariant basis number, any two bases of the same
  module have index types of equal cardinality. This file contains no proof.
*)

From Stdlib Require Import List Vectors.Fin.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.

Record q3527205_semiring (R : Type) : Type := {
  q3527205_zero : R;
  q3527205_one : R;
  q3527205_add : R -> R -> R;
  q3527205_mul : R -> R -> R;
  q3527205_add_assoc :
    forall x y z : R,
      q3527205_add x (q3527205_add y z) =
      q3527205_add (q3527205_add x y) z;
  q3527205_add_comm :
    forall x y : R,
      q3527205_add x y = q3527205_add y x;
  q3527205_zero_add :
    forall x : R, q3527205_add q3527205_zero x = x;
  q3527205_add_zero :
    forall x : R, q3527205_add x q3527205_zero = x;
  q3527205_mul_assoc :
    forall x y z : R,
      q3527205_mul x (q3527205_mul y z) =
      q3527205_mul (q3527205_mul x y) z;
  q3527205_one_mul :
    forall x : R, q3527205_mul q3527205_one x = x;
  q3527205_mul_one :
    forall x : R, q3527205_mul x q3527205_one = x;
  q3527205_mul_add :
    forall x y z : R,
      q3527205_mul x (q3527205_add y z) =
      q3527205_add
        (q3527205_mul x y) (q3527205_mul x z);
  q3527205_add_mul :
    forall x y z : R,
      q3527205_mul (q3527205_add x y) z =
      q3527205_add
        (q3527205_mul x z) (q3527205_mul y z);
  q3527205_zero_mul :
    forall x : R, q3527205_mul q3527205_zero x = q3527205_zero;
  q3527205_mul_zero :
    forall x : R, q3527205_mul x q3527205_zero = q3527205_zero
}.

Arguments q3527205_zero {R} _.
Arguments q3527205_one {R} _.
Arguments q3527205_add {R} _ _ _.
Arguments q3527205_mul {R} _ _ _.

Record q3527205_module
    {R : Type}
    (S : q3527205_semiring R)
    (M : Type) : Type := {
  q3527205_mzero : M;
  q3527205_madd : M -> M -> M;
  q3527205_smul : R -> M -> M;
  q3527205_madd_assoc :
    forall x y z : M,
      q3527205_madd x (q3527205_madd y z) =
      q3527205_madd (q3527205_madd x y) z;
  q3527205_madd_comm :
    forall x y : M,
      q3527205_madd x y = q3527205_madd y x;
  q3527205_mzero_add :
    forall x : M, q3527205_madd q3527205_mzero x = x;
  q3527205_madd_zero :
    forall x : M, q3527205_madd x q3527205_mzero = x;
  q3527205_one_smul :
    forall x : M, q3527205_smul (q3527205_one S) x = x;
  q3527205_mul_smul :
    forall (r s : R) (x : M),
      q3527205_smul (q3527205_mul S r s) x =
      q3527205_smul r (q3527205_smul s x);
  q3527205_add_smul :
    forall (r s : R) (x : M),
      q3527205_smul (q3527205_add S r s) x =
      q3527205_madd
        (q3527205_smul r x) (q3527205_smul s x);
  q3527205_smul_add :
    forall (r : R) (x y : M),
      q3527205_smul r (q3527205_madd x y) =
      q3527205_madd
        (q3527205_smul r x) (q3527205_smul r y);
  q3527205_zero_smul :
    forall x : M,
      q3527205_smul (q3527205_zero S) x = q3527205_mzero;
  q3527205_smul_zero :
    forall r : R,
      q3527205_smul r q3527205_mzero = q3527205_mzero
}.

Arguments q3527205_mzero {R S M} _.
Arguments q3527205_madd {R S M} _ _ _.
Arguments q3527205_smul {R S M} _ _ _.

Fixpoint q3527205_linear_combination
    {R M : Type}
    {S : q3527205_semiring R}
    (V : q3527205_module S M)
    {I : Type}
    (vectors : I -> M)
    (terms : list (I * R)) : M :=
  match terms with
  | nil => q3527205_mzero V
  | (i, r) :: rest =>
      q3527205_madd V
        (q3527205_smul V r (vectors i))
        (q3527205_linear_combination V vectors rest)
  end.

Definition q3527205_exact_finite_support
    {R : Type}
    {S : q3527205_semiring R}
    {I : Type}
    (coefficients : I -> R)
    (terms : list (I * R)) : Prop :=
  NoDup (map (@fst I R) terms) /\
  Forall
    (fun term => snd term = coefficients (fst term))
    terms /\
  forall i : I,
    In i (map (@fst I R) terms) <->
    coefficients i <> q3527205_zero S.

Definition q3527205_represents
    {R M : Type}
    {S : q3527205_semiring R}
    (V : q3527205_module S M)
    {I : Type}
    (vectors : I -> M)
    (x : M)
  (coefficients : I -> R) : Prop :=
  exists terms : list (I * R),
    @q3527205_exact_finite_support R S I coefficients terms /\
    q3527205_linear_combination V vectors terms = x.

Record q3527205_basis
    {R M : Type}
    {S : q3527205_semiring R}
    (V : q3527205_module S M)
    (I : Type) : Type := {
  q3527205_basis_vector : I -> M;
  q3527205_basis_representation :
    forall x : M,
      exists coefficients : I -> R,
        q3527205_represents
          V q3527205_basis_vector x coefficients /\
        forall other : I -> R,
          q3527205_represents
            V q3527205_basis_vector x other ->
          forall i : I, other i = coefficients i
}.

Arguments q3527205_basis_vector {R M S V I} _ _.

Record q3527205_fin_linear_equiv
    {R : Type}
    (S : q3527205_semiring R)
    (n m : nat) : Type := {
  q3527205_fin_forward : (Fin.t n -> R) -> (Fin.t m -> R);
  q3527205_fin_backward : (Fin.t m -> R) -> (Fin.t n -> R);
  q3527205_fin_forward_add :
    forall (x y : Fin.t n -> R) (i : Fin.t m),
      q3527205_fin_forward
        (fun j => q3527205_add S (x j) (y j)) i =
      q3527205_add S
        (q3527205_fin_forward x i)
        (q3527205_fin_forward y i);
  q3527205_fin_forward_smul :
    forall (r : R) (x : Fin.t n -> R) (i : Fin.t m),
      q3527205_fin_forward
        (fun j => q3527205_mul S r (x j)) i =
      q3527205_mul S r (q3527205_fin_forward x i);
  q3527205_fin_left_inverse :
    forall (x : Fin.t n -> R) (i : Fin.t n),
      q3527205_fin_backward (q3527205_fin_forward x) i = x i;
  q3527205_fin_right_inverse :
    forall (y : Fin.t m -> R) (i : Fin.t m),
      q3527205_fin_forward (q3527205_fin_backward y) i = y i
}.

Record q3527205_invariant_basis_number
    {R : Type}
    (S : q3527205_semiring R) : Prop := {
  q3527205_eq_of_fin_equiv :
    forall n m : nat,
      q3527205_fin_linear_equiv S n m -> n = m
}.

Definition q3527205_bijection (A B : Type) : Prop :=
  exists (forward : A -> B) (backward : B -> A),
    (forall x : A, backward (forward x) = x) /\
    (forall y : B, forward (backward y) = y).

Theorem mk_eq_mk_of_basis :
  forall (R M I I' : Type)
         (S : q3527205_semiring R)
         (V : q3527205_module S M)
         (v : q3527205_basis V I)
         (v' : q3527205_basis V I'),
    q3527205_invariant_basis_number S ->
    q3527205_bijection I I'.
Admitted.
