(* Statement-only formalization of PutnamBench corpus artifact putnam_2020_b4:
   the reciprocal average associated with balanced integer unit-step paths of
   length 2n, evaluated at n = 2020. This file contains no proof. *)

From Stdlib Require Import Reals ZArith Lists.List Arith.PeanoNat.

Import ListNotations.
Open Scope R_scope.

Definition putnam_2020_b4_step (direction : bool) : Z :=
  if direction then 1%Z else (-1)%Z.

Fixpoint putnam_2020_b4_height_after
    (directions : list bool) (j : nat) : Z :=
  match j, directions with
  | O, _ => 0%Z
  | S _, [] => 0%Z
  | S k, direction :: remaining =>
      (putnam_2020_b4_step direction +
       putnam_2020_b4_height_after remaining k)%Z
  end.

Fixpoint putnam_2020_b4_bit_words (length : nat) : list (list bool) :=
  match length with
  | O => [[]]
  | S k =>
      map (cons true) (putnam_2020_b4_bit_words k) ++
      map (cons false) (putnam_2020_b4_bit_words k)
  end.

Definition putnam_2020_b4_balanced (directions : list bool) : bool :=
  Z.eqb
    (putnam_2020_b4_height_after directions (length directions))
    0%Z.

Definition putnam_2020_b4_paths (n : nat) : list (list bool) :=
  filter putnam_2020_b4_balanced
    (putnam_2020_b4_bit_words (2 * n)).

Definition putnam_2020_b4_three_to_integer (exponent : Z) : R :=
  match exponent with
  | Z0 => 1
  | Zpos p => 3 ^ Pos.to_nat p
  | Zneg p => / (3 ^ Pos.to_nat p)
  end.

Definition putnam_2020_b4_q
    (n : nat) (directions : list bool) : R :=
  1 +
  fold_right Rplus 0
    (map
      (fun j : nat =>
        putnam_2020_b4_three_to_integer
          (putnam_2020_b4_height_after directions j))
      (seq 1 (2 * n - 1))).

Definition putnam_2020_b4_M (n : nat) : R :=
  let paths := putnam_2020_b4_paths n in
  fold_right Rplus 0
    (map (fun directions => / putnam_2020_b4_q n directions) paths) /
  INR (length paths).

Definition putnam_2020_b4_solution : R := 1 / 4040.

Theorem putnam_2020_b4 :
  putnam_2020_b4_M 2020 = putnam_2020_b4_solution.
Admitted.
