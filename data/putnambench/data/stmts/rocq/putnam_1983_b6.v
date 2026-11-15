(* Statement-only formalization of PutnamBench artifact putnam_1983_b6:
   existence of integer-coefficient polynomials whose squared values at a
   nontrivial complex (2^n + 1)-st root of unity sum to -1; this file contains
   no proof. *)

From Stdlib Require Import Reals ZArith List Arith.

Definition putnam_1983_b6_complex := (R * R)%type.

Definition putnam_1983_b6_zero : putnam_1983_b6_complex := (0%R, 0%R).
Definition putnam_1983_b6_one : putnam_1983_b6_complex := (1%R, 0%R).

Definition putnam_1983_b6_of_Z (a : Z) : putnam_1983_b6_complex :=
  (IZR a, 0%R).

Definition putnam_1983_b6_add
    (z w : putnam_1983_b6_complex) : putnam_1983_b6_complex :=
  ((fst z + fst w)%R, (snd z + snd w)%R).

Definition putnam_1983_b6_neg
    (z : putnam_1983_b6_complex) : putnam_1983_b6_complex :=
  ((- fst z)%R, (- snd z)%R).

Definition putnam_1983_b6_sub
    (z w : putnam_1983_b6_complex) : putnam_1983_b6_complex :=
  putnam_1983_b6_add z (putnam_1983_b6_neg w).

Definition putnam_1983_b6_mul
    (z w : putnam_1983_b6_complex) : putnam_1983_b6_complex :=
  ((fst z * fst w - snd z * snd w)%R,
   (fst z * snd w + snd z * fst w)%R).

Fixpoint putnam_1983_b6_pow
    (z : putnam_1983_b6_complex) (k : nat) : putnam_1983_b6_complex :=
  match k with
  | O => putnam_1983_b6_one
  | S j => putnam_1983_b6_mul z (putnam_1983_b6_pow z j)
  end.

Fixpoint putnam_1983_b6_eval
    (coefficients : list Z)
    (z : putnam_1983_b6_complex) : putnam_1983_b6_complex :=
  match coefficients with
  | nil => putnam_1983_b6_zero
  | coefficient :: remaining =>
      putnam_1983_b6_add
        (putnam_1983_b6_of_Z coefficient)
        (putnam_1983_b6_mul z
          (putnam_1983_b6_eval remaining z))
  end.

Theorem putnam_1983_b6
    (n : nat)
    (npos : (0 < n)%nat)
    (alpha : putnam_1983_b6_complex)
    (halpha :
      putnam_1983_b6_sub
        (putnam_1983_b6_pow alpha (Nat.pow 2 n + 1))
        putnam_1983_b6_one =
      putnam_1983_b6_zero /\
      alpha <> putnam_1983_b6_one) :
  exists p q : list Z,
    putnam_1983_b6_add
      (putnam_1983_b6_pow (putnam_1983_b6_eval p alpha) 2)
      (putnam_1983_b6_pow (putnam_1983_b6_eval q alpha) 2) =
    putnam_1983_b6_neg putnam_1983_b6_one.
Admitted.
