(*
  Statement-only formalization of Thousand Theorems corpus artifact Q7433182
  (thousand-theorems__rocq__Q7433182), "Schwartz–Zippel theorem": a nonzero
  multivariate polynomial over an integral domain has, on a product of finite
  sample sets, a zero fraction bounded by the maximum over its supported
  monomials of the sum of coordinate degrees divided by sample-set sizes.
  This file contains no proof.
*)

From Stdlib Require Import List Arith.PeanoNat ZArith QArith.QArith.

Import ListNotations.
Open Scope Q_scope.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q7433182_commutative_integral_domain (R : Type) : Type := {
  q7433182_zero : R;
  q7433182_one : R;
  q7433182_add : R -> R -> R;
  q7433182_mul : R -> R -> R;
  q7433182_neg : R -> R;
  q7433182_add_assoc :
    forall x y z : R,
      q7433182_add x (q7433182_add y z) =
      q7433182_add (q7433182_add x y) z;
  q7433182_add_comm :
    forall x y : R,
      q7433182_add x y = q7433182_add y x;
  q7433182_add_zero :
    forall x : R,
      q7433182_add x q7433182_zero = x;
  q7433182_add_neg :
    forall x : R,
      q7433182_add x (q7433182_neg x) = q7433182_zero;
  q7433182_mul_assoc :
    forall x y z : R,
      q7433182_mul x (q7433182_mul y z) =
      q7433182_mul (q7433182_mul x y) z;
  q7433182_mul_comm :
    forall x y : R,
      q7433182_mul x y = q7433182_mul y x;
  q7433182_mul_one :
    forall x : R,
      q7433182_mul x q7433182_one = x;
  q7433182_mul_add :
    forall x y z : R,
      q7433182_mul x (q7433182_add y z) =
      q7433182_add
        (q7433182_mul x y) (q7433182_mul x z);
  q7433182_one_ne_zero :
    q7433182_one <> q7433182_zero;
  q7433182_no_zero_divisors :
    forall x y : R,
      q7433182_mul x y = q7433182_zero ->
      x = q7433182_zero \/ y = q7433182_zero
}.

Arguments q7433182_zero {R} _.
Arguments q7433182_one {R} _.
Arguments q7433182_add {R} _ _ _.
Arguments q7433182_mul {R} _ _ _.
Arguments q7433182_neg {R} _ _.

Record q7433182_vector (A : Type) (n : nat) : Type := {
  q7433182_vector_elements : list A;
  q7433182_vector_length :
    length q7433182_vector_elements = n
}.

Arguments q7433182_vector_elements {A n} _.

Record q7433182_finset (A : Type) : Type := {
  q7433182_finset_elements : list A;
  q7433182_finset_nodup :
    NoDup q7433182_finset_elements
}.

Arguments q7433182_finset_elements {A} _.

Definition q7433182_monomial (n : nat) : Type :=
  q7433182_vector nat n.

Definition q7433182_polynomial (R : Type) (n : nat) : Type :=
  list (q7433182_monomial n * R).

Fixpoint q7433182_nat_list_eqb
    (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      Nat.eqb x y && q7433182_nat_list_eqb xs' ys'
  | _, _ => false
  end.

Fixpoint q7433182_pow
    {R : Type}
    (D : q7433182_commutative_integral_domain R)
    (x : R) (n : nat) : R :=
  match n with
  | O => q7433182_one D
  | S k => q7433182_mul D x (q7433182_pow D x k)
  end.

Fixpoint q7433182_coefficient
    {R : Type} {n : nat}
    (D : q7433182_commutative_integral_domain R)
    (terms : q7433182_polynomial R n)
    (exponents : list nat) : R :=
  match terms with
  | [] => q7433182_zero D
  | (m, c) :: rest =>
      if q7433182_nat_list_eqb
          (q7433182_vector_elements m) exponents
      then
        q7433182_add D c
          (q7433182_coefficient D rest exponents)
      else q7433182_coefficient D rest exponents
  end.

Fixpoint q7433182_monomial_mem
    (m : list nat) (monomials : list (list nat)) : bool :=
  match monomials with
  | [] => false
  | x :: rest =>
      if q7433182_nat_list_eqb m x
      then true
      else q7433182_monomial_mem m rest
  end.

Fixpoint q7433182_collect_monomials
    {R : Type} {n : nat}
    (terms : q7433182_polynomial R n) : list (list nat) :=
  match terms with
  | [] => []
  | (m, _) :: rest =>
      let collected := q7433182_collect_monomials rest in
      let exponents := q7433182_vector_elements m in
      if q7433182_monomial_mem exponents collected
      then collected
      else exponents :: collected
  end.

Fixpoint q7433182_filter_support
    {R : Type} {n : nat}
    (D : q7433182_commutative_integral_domain R)
    (eq_dec : forall x y : R, {x = y} + {x <> y})
    (terms : q7433182_polynomial R n)
    (monomials : list (list nat)) : list (list nat) :=
  match monomials with
  | [] => []
  | m :: rest =>
      if eq_dec (q7433182_coefficient D terms m) (q7433182_zero D)
      then q7433182_filter_support D eq_dec terms rest
      else m :: q7433182_filter_support D eq_dec terms rest
  end.

Definition q7433182_support
    {R : Type} {n : nat}
    (D : q7433182_commutative_integral_domain R)
    (eq_dec : forall x y : R, {x = y} + {x <> y})
    (p : q7433182_polynomial R n) : list (list nat) :=
  q7433182_filter_support D eq_dec p
    (q7433182_collect_monomials p).

Definition q7433182_polynomial_nonzero
    {R : Type} {n : nat}
    (D : q7433182_commutative_integral_domain R)
    (eq_dec : forall x y : R, {x = y} + {x <> y})
    (p : q7433182_polynomial R n) : Prop :=
  q7433182_support D eq_dec p <> [].

Fixpoint q7433182_monomial_value
    {R : Type}
    (D : q7433182_commutative_integral_domain R)
    (exponents : list nat)
    (point : list R) : R :=
  match exponents, point with
  | [], [] => q7433182_one D
  | exponent :: exponents', x :: point' =>
      q7433182_mul D
        (q7433182_pow D x exponent)
        (q7433182_monomial_value D exponents' point')
  | _, _ => q7433182_one D
  end.

Fixpoint q7433182_evaluate
    {R : Type} {n : nat}
    (D : q7433182_commutative_integral_domain R)
    (point : list R)
    (p : q7433182_polynomial R n) : R :=
  match p with
  | [] => q7433182_zero D
  | (m, c) :: rest =>
      q7433182_add D
        (q7433182_mul D c
          (q7433182_monomial_value D
            (q7433182_vector_elements m) point))
        (q7433182_evaluate D point rest)
  end.

Fixpoint q7433182_cartesian_product
    {R : Type}
    (sets : list (q7433182_finset R)) : list (list R) :=
  match sets with
  | [] => [[]]
  | set :: rest =>
      flat_map
        (fun x =>
          map (fun point => x :: point)
            (q7433182_cartesian_product rest))
        (q7433182_finset_elements set)
  end.

Fixpoint q7433182_zero_count
    {R : Type} {n : nat}
    (D : q7433182_commutative_integral_domain R)
    (eq_dec : forall x y : R, {x = y} + {x <> y})
    (p : q7433182_polynomial R n)
    (points : list (list R)) : nat :=
  match points with
  | [] => O
  | point :: rest =>
      if eq_dec (q7433182_evaluate D point p) (q7433182_zero D)
      then S (q7433182_zero_count D eq_dec p rest)
      else q7433182_zero_count D eq_dec p rest
  end.

Definition q7433182_nat_to_Q (n : nat) : Q :=
  inject_Z (Z.of_nat n).

Fixpoint q7433182_cardinality_product
    {R : Type}
    (sets : list (q7433182_finset R)) : Q :=
  match sets with
  | [] => 1
  | set :: rest =>
      q7433182_nat_to_Q
        (length (q7433182_finset_elements set)) *
      q7433182_cardinality_product rest
  end.

Fixpoint q7433182_exponent_ratio_sum
    {R : Type}
    (exponents : list nat)
    (sets : list (q7433182_finset R)) : Q :=
  match exponents, sets with
  | [], [] => 0
  | exponent :: exponents', set :: sets' =>
      q7433182_nat_to_Q exponent /
        q7433182_nat_to_Q
          (length (q7433182_finset_elements set)) +
      q7433182_exponent_ratio_sum exponents' sets'
  | _, _ => 0
  end.

Definition q7433182_Qmax (x y : Q) : Q :=
  if Qle_bool x y then y else x.

Fixpoint q7433182_support_sup_sum
    {R : Type}
    (support : list (list nat))
    (sets : list (q7433182_finset R)) : Q :=
  match support with
  | [] => 0
  | monomial :: rest =>
      q7433182_Qmax
        (q7433182_exponent_ratio_sum monomial sets)
        (q7433182_support_sup_sum rest sets)
  end.

Theorem MvPolynomial_schwartz_zippel_sup_sum :
  forall
    (R : Type)
    (D : q7433182_commutative_integral_domain R)
    (eq_dec : forall x y : R, {x = y} + {x <> y})
    (n : nat)
    (p : q7433182_polynomial R n),
    q7433182_polynomial_nonzero D eq_dec p ->
    forall S : q7433182_vector (q7433182_finset R) n,
      q7433182_nat_to_Q
        (q7433182_zero_count D eq_dec p
          (q7433182_cartesian_product
            (q7433182_vector_elements S))) /
        q7433182_cardinality_product
          (q7433182_vector_elements S)
      <=
      q7433182_support_sup_sum
        (q7433182_support D eq_dec p)
        (q7433182_vector_elements S).
Admitted.
