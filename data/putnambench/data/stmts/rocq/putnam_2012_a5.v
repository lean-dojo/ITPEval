(* Statement-only formalization of PutnamBench corpus artifact putnam_2012_a5:
   classification of finite-field affine maps whose orbit of zero visits all
   p^n vectors without repetition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Vectors.Fin.

Record putnam_2012_a5_finite_field : Type := {
  ff_carrier : Type;
  ff_zero : ff_carrier;
  ff_one : ff_carrier;
  ff_add : ff_carrier -> ff_carrier -> ff_carrier;
  ff_mul : ff_carrier -> ff_carrier -> ff_carrier;
  ff_opp : ff_carrier -> ff_carrier;
  ff_inv : ff_carrier -> ff_carrier;
  ff_zero_neq_one : ff_zero <> ff_one;
  ff_add_assoc :
    forall x y z, ff_add x (ff_add y z) = ff_add (ff_add x y) z;
  ff_add_comm : forall x y, ff_add x y = ff_add y x;
  ff_add_zero_l : forall x, ff_add ff_zero x = x;
  ff_add_zero_r : forall x, ff_add x ff_zero = x;
  ff_add_opp_l : forall x, ff_add (ff_opp x) x = ff_zero;
  ff_add_opp_r : forall x, ff_add x (ff_opp x) = ff_zero;
  ff_mul_assoc :
    forall x y z, ff_mul x (ff_mul y z) = ff_mul (ff_mul x y) z;
  ff_mul_comm : forall x y, ff_mul x y = ff_mul y x;
  ff_mul_one_l : forall x, ff_mul ff_one x = x;
  ff_mul_one_r : forall x, ff_mul x ff_one = x;
  ff_mul_add_l :
    forall x y z, ff_mul x (ff_add y z) = ff_add (ff_mul x y) (ff_mul x z);
  ff_mul_add_r :
    forall x y z, ff_mul (ff_add x y) z = ff_add (ff_mul x z) (ff_mul y z);
  ff_inv_zero : ff_inv ff_zero = ff_zero;
  ff_inv_l :
    forall x, x <> ff_zero -> ff_mul (ff_inv x) x = ff_one;
  ff_inv_r :
    forall x, x <> ff_zero -> ff_mul x (ff_inv x) = ff_one;
  ff_elements : list ff_carrier;
  ff_elements_nodup : NoDup ff_elements;
  ff_elements_complete : forall x, In x ff_elements
}.

Definition putnam_2012_a5_prime (p : nat) : Prop :=
  2 <= p /\
  forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition putnam_2012_a5_solution (q : nat * nat) : Prop :=
  fst q = 1%nat \/ q = (2%nat, 2%nat).

Definition putnam_2012_a5_vector
    (K : putnam_2012_a5_finite_field) (n : nat) : Type :=
  Fin.t n -> ff_carrier K.

Definition putnam_2012_a5_vector_eq
    (K : putnam_2012_a5_finite_field) (n : nat)
    (x y : putnam_2012_a5_vector K n) : Prop :=
  forall i : Fin.t n, x i = y i.

Definition putnam_2012_a5_matrix
    (K : putnam_2012_a5_finite_field) (n : nat) : Type :=
  Fin.t n -> Fin.t n -> ff_carrier K.

Fixpoint putnam_2012_a5_fin_sum
    (K : putnam_2012_a5_finite_field) (n : nat)
    : (Fin.t n -> ff_carrier K) -> ff_carrier K :=
  match n as m return (Fin.t m -> ff_carrier K) -> ff_carrier K with
  | 0 => fun _ => ff_zero K
  | S m =>
      fun f =>
        ff_add K (f Fin.F1)
          (putnam_2012_a5_fin_sum K m (fun i => f (Fin.FS i)))
  end.

Definition putnam_2012_a5_zero_vector
    (K : putnam_2012_a5_finite_field) (n : nat)
    : putnam_2012_a5_vector K n :=
  fun _ => ff_zero K.

Definition putnam_2012_a5_matrix_vector
    (K : putnam_2012_a5_finite_field) (n : nat)
    (M : putnam_2012_a5_matrix K n)
    (x : putnam_2012_a5_vector K n)
    : putnam_2012_a5_vector K n :=
  fun i =>
    putnam_2012_a5_fin_sum K n
      (fun j => ff_mul K (M i j) (x j)).

Definition putnam_2012_a5_affine
    (K : putnam_2012_a5_finite_field) (n : nat)
    (M : putnam_2012_a5_matrix K n)
    (v x : putnam_2012_a5_vector K n)
    : putnam_2012_a5_vector K n :=
  fun i => ff_add K (v i) (putnam_2012_a5_matrix_vector K n M x i).

Fixpoint putnam_2012_a5_iterate
    {A : Type} (k : nat) (f : A -> A) (x : A) : A :=
  match k with
  | 0 => x
  | S m => f (putnam_2012_a5_iterate m f x)
  end.

Theorem putnam_2012_a5
    (n p : nat)
    (hn : 0 < n)
    (hp : putnam_2012_a5_prime p)
    (K : putnam_2012_a5_finite_field)
    (hcard : length (ff_elements K) = p) :
  putnam_2012_a5_solution (n, p) <->
  exists (M : putnam_2012_a5_matrix K n)
         (v : putnam_2012_a5_vector K n),
    forall i j : Fin.t (Nat.pow p n),
      i <> j ->
      ~ putnam_2012_a5_vector_eq K n
          (putnam_2012_a5_iterate
            (S (proj1_sig (Fin.to_nat i)))
            (putnam_2012_a5_affine K n M v)
            (putnam_2012_a5_zero_vector K n))
          (putnam_2012_a5_iterate
            (S (proj1_sig (Fin.to_nat j)))
            (putnam_2012_a5_affine K n M v)
            (putnam_2012_a5_zero_vector K n)).
Admitted.
