(* Statement-only formalization of PutnamBench corpus artifact putnam_1989_a6:
   a binary-defined formal power series over the field with two elements
   satisfies a cubic power-series identity. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Record putnam_1989_a6_field : Type := {
  p89_field_carrier : Type;
  p89_field_zero : p89_field_carrier;
  p89_field_one : p89_field_carrier;
  p89_field_add :
    p89_field_carrier -> p89_field_carrier -> p89_field_carrier;
  p89_field_mul :
    p89_field_carrier -> p89_field_carrier -> p89_field_carrier;
  p89_field_opp : p89_field_carrier -> p89_field_carrier;
  p89_field_inv : p89_field_carrier -> p89_field_carrier;
  p89_field_add_assoc :
    forall x y z,
      p89_field_add x (p89_field_add y z) =
      p89_field_add (p89_field_add x y) z;
  p89_field_add_comm :
    forall x y, p89_field_add x y = p89_field_add y x;
  p89_field_add_zero :
    forall x, p89_field_add p89_field_zero x = x;
  p89_field_add_opp :
    forall x, p89_field_add (p89_field_opp x) x = p89_field_zero;
  p89_field_mul_assoc :
    forall x y z,
      p89_field_mul x (p89_field_mul y z) =
      p89_field_mul (p89_field_mul x y) z;
  p89_field_mul_comm :
    forall x y, p89_field_mul x y = p89_field_mul y x;
  p89_field_mul_one :
    forall x, p89_field_mul p89_field_one x = x;
  p89_field_mul_add :
    forall x y z,
      p89_field_mul x (p89_field_add y z) =
      p89_field_add (p89_field_mul x y) (p89_field_mul x z);
  p89_field_zero_neq_one : p89_field_zero <> p89_field_one;
  p89_field_mul_inv :
    forall x,
      x <> p89_field_zero ->
      p89_field_mul (p89_field_inv x) x = p89_field_one
}.

Definition putnam_1989_a6_has_two_elements
    (F : putnam_1989_a6_field) : Prop :=
  forall x : p89_field_carrier F,
    x = p89_field_zero F \/ x = p89_field_one F.

Definition putnam_1989_a6_fps
    (F : putnam_1989_a6_field) : Type :=
  nat -> p89_field_carrier F.

Fixpoint putnam_1989_a6_sum_upto
    (F : putnam_1989_a6_field)
    (n : nat)
    (term : nat -> p89_field_carrier F)
    : p89_field_carrier F :=
  match n with
  | O => term O
  | S k =>
      p89_field_add F
        (putnam_1989_a6_sum_upto F k term)
        (term (S k))
  end.

Definition putnam_1989_a6_fps_add
    (F : putnam_1989_a6_field)
    (a b : putnam_1989_a6_fps F)
    : putnam_1989_a6_fps F :=
  fun n => p89_field_add F (a n) (b n).

Definition putnam_1989_a6_fps_mul
    (F : putnam_1989_a6_field)
    (a b : putnam_1989_a6_fps F)
    : putnam_1989_a6_fps F :=
  fun n =>
    putnam_1989_a6_sum_upto F n
      (fun i => p89_field_mul F (a i) (b (Nat.sub n i))).

Definition putnam_1989_a6_fps_zero
    (F : putnam_1989_a6_field)
    : putnam_1989_a6_fps F :=
  fun _ => p89_field_zero F.

Definition putnam_1989_a6_fps_one
    (F : putnam_1989_a6_field)
    : putnam_1989_a6_fps F :=
  fun n =>
    if Nat.eqb n O
    then p89_field_one F
    else p89_field_zero F.

Definition putnam_1989_a6_fps_X
    (F : putnam_1989_a6_field)
    : putnam_1989_a6_fps F :=
  fun n =>
    if Nat.eqb n 1
    then p89_field_one F
    else p89_field_zero F.

Definition putnam_1989_a6_fps_cube
    (F : putnam_1989_a6_field)
    (a : putnam_1989_a6_fps F)
    : putnam_1989_a6_fps F :=
  putnam_1989_a6_fps_mul F
    (putnam_1989_a6_fps_mul F a a) a.

Definition putnam_1989_a6_fps_eq
    (F : putnam_1989_a6_field)
    (a b : putnam_1989_a6_fps F) : Prop :=
  forall n : nat, a n = b n.

Fixpoint putnam_1989_a6_binary_digits_fuel
    (fuel n : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
      if Nat.eqb n O
      then []
      else
        Nat.modulo n 2 ::
        putnam_1989_a6_binary_digits_fuel fuel' (Nat.div n 2)
  end.

Definition putnam_1989_a6_binary_digits (n : nat) : list nat :=
  putnam_1989_a6_binary_digits_fuel (S n) n.

Definition putnam_1989_a6_zeros_between
    (bin : list nat) (i j : nat) : bool :=
  forallb
    (fun k =>
      orb
        (negb (andb (Nat.ltb i k) (Nat.ltb k j)))
        (Nat.eqb (nth k bin O) O))
    (seq O (length bin)).

Definition putnam_1989_a6_pair_condition
    (bin : list nat) (i j : nat) : bool :=
  let endpoints_and_zero_block :=
    andb
      (Nat.ltb i j)
      (andb
        (Nat.eqb (nth i bin O) 1)
        (andb
          (Nat.eqb (nth j bin O) 1)
          (putnam_1989_a6_zeros_between bin i j))) in
  orb
    (negb endpoints_and_zero_block)
    (Nat.even (Nat.sub (Nat.sub j i) 1)).

Definition putnam_1989_a6_all_zero_blocks_even
    (bin : list nat) : bool :=
  let indices := seq O (length bin) in
  forallb
    (fun i =>
      forallb
        (fun j => putnam_1989_a6_pair_condition bin i j)
        indices)
    indices.

Definition putnam_1989_a6_coefficient_is_one (n : nat) : bool :=
  putnam_1989_a6_all_zero_blocks_even
    (1 :: (putnam_1989_a6_binary_digits n ++ [1])).

Theorem putnam_1989_a6
    (F : putnam_1989_a6_field)
    (hF : putnam_1989_a6_has_two_elements F)
    (alpha : putnam_1989_a6_fps F)
    (h_alpha :
      forall n : nat,
        alpha n =
          if putnam_1989_a6_coefficient_is_one n
          then p89_field_one F
          else p89_field_zero F) :
  putnam_1989_a6_fps_eq F
    (putnam_1989_a6_fps_add F
      (putnam_1989_a6_fps_add F
        (putnam_1989_a6_fps_cube F alpha)
        (putnam_1989_a6_fps_mul F
          (putnam_1989_a6_fps_X F) alpha))
      (putnam_1989_a6_fps_one F))
    (putnam_1989_a6_fps_zero F).
Admitted.
