(* Statement-only formalization of PutnamBench artifact putnam_1979_b3:
   counting constant shifts of an irreducible quadratic over a finite field
   of odd cardinality. This file contains no proof. *)

From Stdlib Require Import List Arith.
Import ListNotations.

Record putnam_1979_b3_finite_field : Type := {
  ff_carrier : Type;
  ff_zero : ff_carrier;
  ff_one : ff_carrier;
  ff_add : ff_carrier -> ff_carrier -> ff_carrier;
  ff_mul : ff_carrier -> ff_carrier -> ff_carrier;
  ff_opp : ff_carrier -> ff_carrier;
  ff_inv : ff_carrier -> ff_carrier;
  ff_add_assoc :
    forall x y z, ff_add x (ff_add y z) = ff_add (ff_add x y) z;
  ff_add_comm : forall x y, ff_add x y = ff_add y x;
  ff_add_zero_l : forall x, ff_add ff_zero x = x;
  ff_add_opp_l : forall x, ff_add (ff_opp x) x = ff_zero;
  ff_mul_assoc :
    forall x y z, ff_mul x (ff_mul y z) = ff_mul (ff_mul x y) z;
  ff_mul_comm : forall x y, ff_mul x y = ff_mul y x;
  ff_mul_one_l : forall x, ff_mul ff_one x = x;
  ff_mul_add_distr_l :
    forall x y z, ff_mul x (ff_add y z) = ff_add (ff_mul x y) (ff_mul x z);
  ff_zero_neq_one : ff_zero <> ff_one;
  ff_mul_inv_l :
    forall x, x <> ff_zero -> ff_mul (ff_inv x) x = ff_one;
  ff_elements : list ff_carrier;
  ff_elements_nodup : NoDup ff_elements;
  ff_elements_complete : forall x : ff_carrier, In x ff_elements
}.

Arguments ff_zero {_}.
Arguments ff_one {_}.
Arguments ff_add {_} _ _.
Arguments ff_mul {_} _ _.

Record putnam_1979_b3_poly2
    (F : putnam_1979_b3_finite_field) : Type := {
  poly2_quadratic : ff_carrier F;
  poly2_linear : ff_carrier F;
  poly2_constant : ff_carrier F
}.

Definition putnam_1979_b3_eval
    {F : putnam_1979_b3_finite_field}
    (p : putnam_1979_b3_poly2 F) (x : ff_carrier F) : ff_carrier F :=
  ff_add
    (ff_add (ff_mul (poly2_quadratic F p) (ff_mul x x))
            (ff_mul (poly2_linear F p) x))
    (poly2_constant F p).

Definition putnam_1979_b3_irreducible
    {F : putnam_1979_b3_finite_field}
    (p : putnam_1979_b3_poly2 F) : Prop :=
  poly2_quadratic F p <> ff_zero /\
  forall x : ff_carrier F, putnam_1979_b3_eval p x <> ff_zero.

Definition putnam_1979_b3_add_constant
    {F : putnam_1979_b3_finite_field}
    (p : putnam_1979_b3_poly2 F) (d : ff_carrier F) :
    putnam_1979_b3_poly2 F :=
  {| poly2_quadratic := poly2_quadratic F p;
     poly2_linear := poly2_linear F p;
     poly2_constant := ff_add (poly2_constant F p) d |}.

Definition putnam_1979_b3_has_cardinality
    {A : Type} (S : A -> Prop) (n : nat) : Prop :=
  exists xs : list A,
    NoDup xs /\
    (forall x : A, In x xs <-> S x) /\
    length xs = n.

Definition putnam_1979_b3_solution (n : nat) : nat := Nat.div (n - 1) 2.

Theorem putnam_1979_b3 :
  forall (F : putnam_1979_b3_finite_field)
         (n : nat)
         (b c : ff_carrier F)
         (p : putnam_1979_b3_poly2 F),
    n = length (ff_elements F) ->
    (exists k : nat, n = 2 * k + 1) ->
    p = {| poly2_quadratic := ff_one;
           poly2_linear := b;
           poly2_constant := c |} ->
    putnam_1979_b3_irreducible p ->
    putnam_1979_b3_has_cardinality
      (fun d : ff_carrier F =>
         putnam_1979_b3_irreducible
           (putnam_1979_b3_add_constant p d))
      (putnam_1979_b3_solution n).
Admitted.
