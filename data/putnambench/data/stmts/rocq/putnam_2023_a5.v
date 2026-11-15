(* Statement-only formalization of PutnamBench corpus artifact putnam_2023_a5:
   the complex zeros of a weighted power sum determined by ternary digit counts;
   this file contains no proof. *)

From Stdlib Require Import Reals.

Definition putnam_2023_a5_complex := (R * R)%type.

Definition putnam_2023_a5_cadd
    (z w : putnam_2023_a5_complex) : putnam_2023_a5_complex :=
  ((fst z + fst w)%R, (snd z + snd w)%R).

Definition putnam_2023_a5_cmul
    (z w : putnam_2023_a5_complex) : putnam_2023_a5_complex :=
  ((fst z * fst w - snd z * snd w)%R,
   (fst z * snd w + snd z * fst w)%R).

Fixpoint putnam_2023_a5_cpow
    (z : putnam_2023_a5_complex) (n : nat) : putnam_2023_a5_complex :=
  match n with
  | O => (1%R, 0%R)
  | S n' => putnam_2023_a5_cmul z (putnam_2023_a5_cpow z n')
  end.

Fixpoint putnam_2023_a5_csum
    (f : nat -> putnam_2023_a5_complex) (n : nat)
    : putnam_2023_a5_complex :=
  match n with
  | O => f O
  | S n' => putnam_2023_a5_cadd (putnam_2023_a5_csum f n') (f (S n'))
  end.

Fixpoint putnam_2023_a5_num_ones_aux (fuel k : nat) : nat :=
  match fuel with
  | O => O
  | S fuel' =>
      (if Nat.eqb (k mod 3) 1 then 1 else 0) +
      putnam_2023_a5_num_ones_aux fuel' (k / 3)
  end.

Definition putnam_2023_a5_num_ones (k : nat) : nat :=
  putnam_2023_a5_num_ones_aux (S k) k.

Definition putnam_2023_a5_center : R :=
  (- (INR (Nat.pow 3 1010) - 1) / 2)%R.

Definition putnam_2023_a5_offset : R :=
  (sqrt (INR (Nat.pow 9 1010) - 1) / 4)%R.

Definition putnam_2023_a5_polynomial
    (z : putnam_2023_a5_complex) : putnam_2023_a5_complex :=
  putnam_2023_a5_csum
    (fun k : nat =>
       putnam_2023_a5_cmul
         (putnam_2023_a5_cpow
            ((-2)%R, 0%R) (putnam_2023_a5_num_ones k))
         (putnam_2023_a5_cpow
            (putnam_2023_a5_cadd z (INR k, 0%R)) 2023))
    (Nat.pow 3 1010 - 1).

Theorem putnam_2023_a5 :
  forall z : putnam_2023_a5_complex,
    putnam_2023_a5_polynomial z = (0%R, 0%R) <->
    z = (putnam_2023_a5_center, 0%R) \/
    z = (putnam_2023_a5_center, putnam_2023_a5_offset) \/
    z = (putnam_2023_a5_center, (- putnam_2023_a5_offset)%R).
Proof.
Admitted.
