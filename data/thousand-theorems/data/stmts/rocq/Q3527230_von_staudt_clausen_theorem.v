(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527230
  (thousand-theorems__rocq__Q3527230), "Von Staudt–Clausen theorem": for every
  natural number k, the even Bernoulli number B_(2k), corrected by the sum of
  1/p over primes p with p - 1 dividing 2k, is an integer. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat Lists.List QArith.QArith
  ZArith.ZArith ZArith.Znumtheory.

Import ListNotations.

Definition q3527230_Q_of_nat (n : nat) : Q :=
  inject_Z (Z.of_nat n).

Fixpoint q3527230_choose (n k : nat) {struct n} : nat :=
  match n with
  | O =>
      match k with
      | O => 1
      | S _ => 0
      end
  | S m =>
      match k with
      | O => 1
      | S j => q3527230_choose m j + q3527230_choose m (S j)
      end
  end.

Fixpoint q3527230_Q_sum (count : nat) (f : nat -> Q) : Q :=
  match count with
  | O => 0
  | S n => Qplus (q3527230_Q_sum n f) (f n)
  end.

Fixpoint q3527230_bernoulli_prime_table (count : nat) : list Q :=
  match count with
  | O => []
  | S n =>
      let previous := q3527230_bernoulli_prime_table n in
      let next :=
        Qminus 1
          (q3527230_Q_sum n
            (fun k =>
              Qmult
                (Qdiv
                  (q3527230_Q_of_nat (q3527230_choose n k))
                  (q3527230_Q_of_nat (Nat.sub n k + 1)))
                (nth k previous 0%Q))) in
      previous ++ [next]
  end.

Definition q3527230_bernoulli_prime (n : nat) : Q :=
  nth n (q3527230_bernoulli_prime_table (S n)) 0%Q.

Fixpoint q3527230_Q_pow (x : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S m => Qmult x (q3527230_Q_pow x m)
  end.

Definition q3527230_bernoulli (n : nat) : Q :=
  Qmult
    (q3527230_Q_pow (inject_Z (-1)) n)
    (q3527230_bernoulli_prime n).

Definition q3527230_prime_term (even_index p : nat) : Q :=
  match Znumtheory.prime_dec (Z.of_nat p) with
  | left _ =>
      if Nat.eq_dec (Nat.modulo even_index (Nat.sub p 1)) 0
      then Qdiv 1 (q3527230_Q_of_nat p)
      else 0
  | right _ => 0
  end.

Fixpoint q3527230_von_staudt_sum (bound even_index : nat) : Q :=
  match bound with
  | O => 0
  | S p =>
      Qplus
        (q3527230_von_staudt_sum p even_index)
        (q3527230_prime_term even_index p)
  end.

Theorem q3527230_von_staudt_clausen :
  forall k : nat,
    exists z : Z,
      Qeq
        (inject_Z z)
        (Qplus
          (q3527230_bernoulli (2 * k))
          (q3527230_von_staudt_sum (2 * k + 2) (2 * k))).
Admitted.
