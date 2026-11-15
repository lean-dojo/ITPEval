(*
  Statement-only formalization of Thousand Theorems corpus artifact Q776578
  (thousand-theorems__rocq__Q776578), "Artin–Wedderburn theorem": a
  semisimple algebra over a commutative semiring is algebra-equivalent to a
  finite product of nonzero-size square matrix algebras over division
  algebras. This file contains no proof.
*)

From Stdlib Require Import Vectors.Fin.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q776578_comm_semiring (A : Type) : Type := {
  q776578_czero : A;
  q776578_cone : A;
  q776578_cadd : A -> A -> A;
  q776578_cmul : A -> A -> A;
  q776578_cadd_assoc :
    forall x y z : A,
      q776578_cadd x (q776578_cadd y z) =
      q776578_cadd (q776578_cadd x y) z;
  q776578_cadd_comm :
    forall x y : A,
      q776578_cadd x y = q776578_cadd y x;
  q776578_czero_add :
    forall x : A, q776578_cadd q776578_czero x = x;
  q776578_cadd_zero :
    forall x : A, q776578_cadd x q776578_czero = x;
  q776578_cmul_assoc :
    forall x y z : A,
      q776578_cmul x (q776578_cmul y z) =
      q776578_cmul (q776578_cmul x y) z;
  q776578_cmul_comm :
    forall x y : A,
      q776578_cmul x y = q776578_cmul y x;
  q776578_cone_mul :
    forall x : A, q776578_cmul q776578_cone x = x;
  q776578_cmul_add :
    forall x y z : A,
      q776578_cmul x (q776578_cadd y z) =
      q776578_cadd
        (q776578_cmul x y)
        (q776578_cmul x z);
  q776578_cadd_mul :
    forall x y z : A,
      q776578_cmul (q776578_cadd x y) z =
      q776578_cadd
        (q776578_cmul x z)
        (q776578_cmul y z);
  q776578_czero_mul :
    forall x : A,
      q776578_cmul q776578_czero x = q776578_czero;
  q776578_cmul_zero :
    forall x : A,
      q776578_cmul x q776578_czero = q776578_czero
}.

Arguments q776578_czero {A} _.
Arguments q776578_cone {A} _.
Arguments q776578_cadd {A} _ _ _.
Arguments q776578_cmul {A} _ _ _.

Record q776578_ring (A : Type) : Type := {
  q776578_zero : A;
  q776578_one : A;
  q776578_add : A -> A -> A;
  q776578_mul : A -> A -> A;
  q776578_neg : A -> A;
  q776578_add_assoc :
    forall x y z : A,
      q776578_add x (q776578_add y z) =
      q776578_add (q776578_add x y) z;
  q776578_add_comm :
    forall x y : A,
      q776578_add x y = q776578_add y x;
  q776578_zero_add :
    forall x : A, q776578_add q776578_zero x = x;
  q776578_add_zero :
    forall x : A, q776578_add x q776578_zero = x;
  q776578_neg_add :
    forall x : A,
      q776578_add (q776578_neg x) x = q776578_zero;
  q776578_add_neg :
    forall x : A,
      q776578_add x (q776578_neg x) = q776578_zero;
  q776578_mul_assoc :
    forall x y z : A,
      q776578_mul x (q776578_mul y z) =
      q776578_mul (q776578_mul x y) z;
  q776578_one_mul :
    forall x : A, q776578_mul q776578_one x = x;
  q776578_mul_one :
    forall x : A, q776578_mul x q776578_one = x;
  q776578_mul_add :
    forall x y z : A,
      q776578_mul x (q776578_add y z) =
      q776578_add
        (q776578_mul x y)
        (q776578_mul x z);
  q776578_add_mul :
    forall x y z : A,
      q776578_mul (q776578_add x y) z =
      q776578_add
        (q776578_mul x z)
        (q776578_mul y z);
  q776578_zero_mul :
    forall x : A,
      q776578_mul q776578_zero x = q776578_zero;
  q776578_mul_zero :
    forall x : A,
      q776578_mul x q776578_zero = q776578_zero
}.

Arguments q776578_zero {A} _.
Arguments q776578_one {A} _.
Arguments q776578_add {A} _ _ _.
Arguments q776578_mul {A} _ _ _.
Arguments q776578_neg {A} _ _.

Record q776578_algebra
    {R0 A : Type}
    (base : q776578_comm_semiring R0)
    (ring : q776578_ring A) : Type := {
  q776578_algebra_map : R0 -> A;
  q776578_algebra_map_zero :
    q776578_algebra_map (q776578_czero base) =
    q776578_zero ring;
  q776578_algebra_map_one :
    q776578_algebra_map (q776578_cone base) =
    q776578_one ring;
  q776578_algebra_map_add :
    forall x y : R0,
      q776578_algebra_map (q776578_cadd base x y) =
      q776578_add ring
        (q776578_algebra_map x)
        (q776578_algebra_map y);
  q776578_algebra_map_mul :
    forall x y : R0,
      q776578_algebra_map (q776578_cmul base x y) =
      q776578_mul ring
        (q776578_algebra_map x)
        (q776578_algebra_map y);
  q776578_algebra_map_commutes :
    forall (r : R0) (x : A),
      q776578_mul ring (q776578_algebra_map r) x =
      q776578_mul ring x (q776578_algebra_map r)
}.

Arguments q776578_algebra_map {R0 A base ring} _ _.

Record q776578_left_ideal
    {A : Type}
    (ring : q776578_ring A) : Type := {
  q776578_left_ideal_mem : A -> Prop;
  q776578_left_ideal_zero :
    q776578_left_ideal_mem (q776578_zero ring);
  q776578_left_ideal_add :
    forall x y : A,
      q776578_left_ideal_mem x ->
      q776578_left_ideal_mem y ->
      q776578_left_ideal_mem (q776578_add ring x y);
  q776578_left_ideal_neg :
    forall x : A,
      q776578_left_ideal_mem x ->
      q776578_left_ideal_mem (q776578_neg ring x);
  q776578_left_ideal_smul :
    forall a x : A,
      q776578_left_ideal_mem x ->
      q776578_left_ideal_mem (q776578_mul ring a x)
}.

Arguments q776578_left_ideal_mem {A ring} _ _.

Definition q776578_are_complements
    {A : Type}
    {ring : q776578_ring A}
    (I J : q776578_left_ideal ring) : Prop :=
  (forall x : A,
    q776578_left_ideal_mem I x ->
    q776578_left_ideal_mem J x ->
    x = q776578_zero ring) /\
  (forall x : A,
    exists i j : A,
      q776578_left_ideal_mem I i /\
      q776578_left_ideal_mem J j /\
      x = q776578_add ring i j).

Definition q776578_is_semisimple_ring
    {A : Type}
    {ring : q776578_ring A} : Prop :=
  forall I : q776578_left_ideal ring,
    exists J : q776578_left_ideal ring,
      q776578_are_complements I J.

Record q776578_division_ring (A : Type) : Type := {
  q776578_division_ring_ring : q776578_ring A;
  q776578_inv : A -> A;
  q776578_zero_ne_one :
    q776578_zero q776578_division_ring_ring <>
    q776578_one q776578_division_ring_ring;
  q776578_inv_zero :
    q776578_inv
      (q776578_zero q776578_division_ring_ring) =
    q776578_zero q776578_division_ring_ring;
  q776578_mul_inv :
    forall x : A,
      x <> q776578_zero q776578_division_ring_ring ->
      q776578_mul q776578_division_ring_ring
        x (q776578_inv x) =
      q776578_one q776578_division_ring_ring;
  q776578_inv_mul :
    forall x : A,
      x <> q776578_zero q776578_division_ring_ring ->
      q776578_mul q776578_division_ring_ring
        (q776578_inv x) x =
      q776578_one q776578_division_ring_ring
}.

Arguments q776578_division_ring_ring {A} _.

Definition q776578_matrix
    (n : nat) (A : Type) : Type :=
  Fin.t n -> Fin.t n -> A.

Fixpoint q776578_fin_sum
    {A : Type}
    (ring : q776578_ring A)
    (n : nat) : (Fin.t n -> A) -> A :=
  match n return (Fin.t n -> A) -> A with
  | 0 => fun _ => q776578_zero ring
  | S k =>
      fun f =>
        q776578_add ring
          (f Fin.F1)
          (@q776578_fin_sum A ring k
            (fun i => f (Fin.FS i)))
  end.

Definition q776578_product_matrix
    {n : nat}
    (D : Fin.t n -> Type)
    (d : forall i : Fin.t n, nat) : Type :=
  forall i : Fin.t n, q776578_matrix (d i) (D i).

Definition q776578_product_equal
    {n : nat}
    {D : Fin.t n -> Type}
    {d : forall i : Fin.t n, nat}
    (X Y : q776578_product_matrix D d) : Prop :=
  forall (i : Fin.t n) (r c : Fin.t (d i)),
    X i r c = Y i r c.

Definition q776578_product_zero
    {n : nat}
    {D : Fin.t n -> Type}
    {d : forall i : Fin.t n, nat}
    (DR : forall i : Fin.t n, q776578_division_ring (D i)) :
    q776578_product_matrix D d :=
  fun i _ _ =>
    q776578_zero (q776578_division_ring_ring (DR i)).

Definition q776578_product_one
    {n : nat}
    {D : Fin.t n -> Type}
    {d : forall i : Fin.t n, nat}
    (DR : forall i : Fin.t n, q776578_division_ring (D i)) :
    q776578_product_matrix D d :=
  fun i r c =>
    if Fin.eq_dec r c
    then q776578_one (q776578_division_ring_ring (DR i))
    else q776578_zero (q776578_division_ring_ring (DR i)).

Definition q776578_product_add
    {n : nat}
    {D : Fin.t n -> Type}
    {d : forall i : Fin.t n, nat}
    (DR : forall i : Fin.t n, q776578_division_ring (D i))
    (X Y : q776578_product_matrix D d) :
    q776578_product_matrix D d :=
  fun i r c =>
    q776578_add
      (q776578_division_ring_ring (DR i))
      (X i r c) (Y i r c).

Definition q776578_product_mul
    {n : nat}
    {D : Fin.t n -> Type}
    {d : forall i : Fin.t n, nat}
    (DR : forall i : Fin.t n, q776578_division_ring (D i))
    (X Y : q776578_product_matrix D d) :
    q776578_product_matrix D d :=
  fun i r c =>
    @q776578_fin_sum (D i)
      (q776578_division_ring_ring (DR i))
      (d i)
      (fun k =>
        q776578_mul
          (q776578_division_ring_ring (DR i))
          (X i r k) (Y i k c)).

Definition q776578_product_algebra_map
    {R0 : Type}
    {n : nat}
    {D : Fin.t n -> Type}
    {d : forall i : Fin.t n, nat}
    {base : q776578_comm_semiring R0}
    {DR : forall i : Fin.t n, q776578_division_ring (D i)}
    (DA : forall i : Fin.t n,
      q776578_algebra base
        (q776578_division_ring_ring (DR i)))
    (a : R0) : q776578_product_matrix D d :=
  fun i r c =>
    if Fin.eq_dec r c
    then q776578_algebra_map (DA i) a
    else q776578_zero (q776578_division_ring_ring (DR i)).

Record q776578_alg_equiv
    {R0 R : Type}
    (base : q776578_comm_semiring R0)
    (ring : q776578_ring R)
    (source_algebra : q776578_algebra base ring)
    (n : nat)
    (D : Fin.t n -> Type)
    (d : forall i : Fin.t n, nat)
    (DR : forall i : Fin.t n, q776578_division_ring (D i))
    (DA : forall i : Fin.t n,
      q776578_algebra base
        (q776578_division_ring_ring (DR i))) : Type := {
  q776578_forward :
    R -> q776578_product_matrix D d;
  q776578_inverse :
    q776578_product_matrix D d -> R;
  q776578_left_inverse :
    forall x : R,
      q776578_inverse (q776578_forward x) = x;
  q776578_right_inverse :
    forall y : q776578_product_matrix D d,
      q776578_product_equal
        (q776578_forward (q776578_inverse y)) y;
  q776578_inverse_respects :
    forall x y : q776578_product_matrix D d,
      q776578_product_equal x y ->
      q776578_inverse x = q776578_inverse y;
  q776578_map_zero :
    q776578_product_equal
      (q776578_forward (q776578_zero ring))
      (q776578_product_zero DR);
  q776578_map_one :
    q776578_product_equal
      (q776578_forward (q776578_one ring))
      (q776578_product_one DR);
  q776578_map_add :
    forall x y : R,
      q776578_product_equal
        (q776578_forward (q776578_add ring x y))
        (q776578_product_add DR
          (q776578_forward x)
          (q776578_forward y));
  q776578_map_mul :
    forall x y : R,
      q776578_product_equal
        (q776578_forward (q776578_mul ring x y))
        (q776578_product_mul DR
          (q776578_forward x)
          (q776578_forward y));
  q776578_map_algebra :
    forall a : R0,
      q776578_product_equal
        (q776578_forward
          (q776578_algebra_map source_algebra a))
        (q776578_product_algebra_map DA a)
}.

Definition q776578_nonempty (A : Type) : Prop :=
  exists _ : A, True.

Section q776578_statement.

Universe q776578_u0 q776578_u.

Theorem IsSemisimpleRing_exists_algEquiv_pi_matrix_divisionRing :
  forall (R0 : Type@{q776578_u0})
         (R : Type@{q776578_u})
         (base : q776578_comm_semiring R0)
         (ring : q776578_ring R)
         (source_algebra : q776578_algebra base ring),
    @q776578_is_semisimple_ring R ring ->
    exists (n : nat)
           (D : Fin.t n -> Type@{q776578_u})
           (d : forall i : Fin.t n, nat)
           (DR : forall i : Fin.t n,
             q776578_division_ring (D i))
           (DA : forall i : Fin.t n,
             q776578_algebra base
               (q776578_division_ring_ring (DR i))),
      (forall i : Fin.t n, d i <> 0) /\
      @q776578_nonempty
        (@q776578_alg_equiv
          R0 R base ring source_algebra n D d DR DA).
Admitted.

End q776578_statement.
