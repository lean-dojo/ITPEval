(* Statement-only formalization of PutnamBench artifact putnam_1987_b3:
   the rational parametrization, over any field of characteristic not two,
   of all solutions to x^2 + y^2 = 1. This file contains no proof. *)

From Stdlib Require Import Ensembles.

Record putnam_1987_b3_field (F : Type) : Type := {
  putnam_1987_b3_zero : F;
  putnam_1987_b3_one : F;
  putnam_1987_b3_add : F -> F -> F;
  putnam_1987_b3_mul : F -> F -> F;
  putnam_1987_b3_opp : F -> F;
  putnam_1987_b3_inv : F -> F;
  putnam_1987_b3_add_assoc :
    forall x y z : F,
      putnam_1987_b3_add x (putnam_1987_b3_add y z) =
      putnam_1987_b3_add (putnam_1987_b3_add x y) z;
  putnam_1987_b3_add_comm :
    forall x y : F,
      putnam_1987_b3_add x y = putnam_1987_b3_add y x;
  putnam_1987_b3_add_zero_l :
    forall x : F,
      putnam_1987_b3_add putnam_1987_b3_zero x = x;
  putnam_1987_b3_add_opp_l :
    forall x : F,
      putnam_1987_b3_add (putnam_1987_b3_opp x) x =
      putnam_1987_b3_zero;
  putnam_1987_b3_mul_assoc :
    forall x y z : F,
      putnam_1987_b3_mul x (putnam_1987_b3_mul y z) =
      putnam_1987_b3_mul (putnam_1987_b3_mul x y) z;
  putnam_1987_b3_mul_comm :
    forall x y : F,
      putnam_1987_b3_mul x y = putnam_1987_b3_mul y x;
  putnam_1987_b3_mul_one_l :
    forall x : F,
      putnam_1987_b3_mul putnam_1987_b3_one x = x;
  putnam_1987_b3_mul_add_distr_l :
    forall x y z : F,
      putnam_1987_b3_mul x (putnam_1987_b3_add y z) =
      putnam_1987_b3_add
        (putnam_1987_b3_mul x y)
        (putnam_1987_b3_mul x z);
  putnam_1987_b3_one_neq_zero :
    putnam_1987_b3_one <> putnam_1987_b3_zero;
  putnam_1987_b3_inv_zero :
    putnam_1987_b3_inv putnam_1987_b3_zero =
    putnam_1987_b3_zero;
  putnam_1987_b3_inv_mul_cancel :
    forall x : F,
      x <> putnam_1987_b3_zero ->
      putnam_1987_b3_mul (putnam_1987_b3_inv x) x =
      putnam_1987_b3_one
}.

Arguments putnam_1987_b3_zero {F} _.
Arguments putnam_1987_b3_one {F} _.
Arguments putnam_1987_b3_add {F} _ _ _.
Arguments putnam_1987_b3_mul {F} _ _ _.
Arguments putnam_1987_b3_opp {F} _ _.
Arguments putnam_1987_b3_inv {F} _ _.

Definition putnam_1987_b3_sub {F : Type}
    (field : putnam_1987_b3_field F) (x y : F) : F :=
  putnam_1987_b3_add field x (putnam_1987_b3_opp field y).

Definition putnam_1987_b3_square {F : Type}
    (field : putnam_1987_b3_field F) (x : F) : F :=
  putnam_1987_b3_mul field x x.

Definition putnam_1987_b3_div {F : Type}
    (field : putnam_1987_b3_field F) (x y : F) : F :=
  putnam_1987_b3_mul field x (putnam_1987_b3_inv field y).

Definition putnam_1987_b3_unit_circle {F : Type}
    (field : putnam_1987_b3_field F) : Ensemble (F * F) :=
  fun p : F * F =>
    putnam_1987_b3_add field
      (putnam_1987_b3_square field (fst p))
      (putnam_1987_b3_square field (snd p)) =
    putnam_1987_b3_one field.

Definition putnam_1987_b3_parametrization {F : Type}
    (field : putnam_1987_b3_field F) : Ensemble (F * F) :=
  fun p : F * F =>
    p = (putnam_1987_b3_one field, putnam_1987_b3_zero field) \/
    exists r : F,
      putnam_1987_b3_square field r <>
        putnam_1987_b3_opp field (putnam_1987_b3_one field) /\
      p =
        (putnam_1987_b3_div field
           (putnam_1987_b3_sub field
             (putnam_1987_b3_square field r)
             (putnam_1987_b3_one field))
           (putnam_1987_b3_add field
             (putnam_1987_b3_square field r)
             (putnam_1987_b3_one field)),
         putnam_1987_b3_div field
           (putnam_1987_b3_mul field
             (putnam_1987_b3_add field
               (putnam_1987_b3_one field)
               (putnam_1987_b3_one field))
             r)
           (putnam_1987_b3_add field
             (putnam_1987_b3_square field r)
             (putnam_1987_b3_one field))).

Theorem putnam_1987_b3 :
  forall (F : Type) (field : putnam_1987_b3_field F),
    putnam_1987_b3_add field
      (putnam_1987_b3_one field)
      (putnam_1987_b3_one field) <>
    putnam_1987_b3_zero field ->
    Same_set (F * F)
      (putnam_1987_b3_unit_circle field)
      (putnam_1987_b3_parametrization field).
Admitted.
