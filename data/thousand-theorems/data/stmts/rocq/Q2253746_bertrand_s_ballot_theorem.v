(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2253746
  (thousand-theorems__rocq__Q2253746), "Bertrand's ballot theorem":
  among vote sequences with p votes for one candidate and q < p for the
  other, the uniform probability of a strictly positive running lead is
  (p - q) / (p + q). This file contains no proof.
*)

From Stdlib Require Import Lists.List ZArith Reals Arith.PeanoNat.

Import ListNotations.

Fixpoint q2253746_sum (l : list Z) : Z :=
  match l with
  | [] => 0%Z
  | x :: xs => (x + q2253746_sum xs)%Z
  end.

Fixpoint q2253746_nonempty_suffixes
    (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | _ :: xs => l :: q2253746_nonempty_suffixes xs
  end.

Definition q2253746_stays_positiveb (l : list Z) : bool :=
  forallb
    (fun suffix => Z.ltb 0%Z (q2253746_sum suffix))
    (q2253746_nonempty_suffixes l).

Definition q2253746_stays_positive (l : list Z) : Prop :=
  q2253746_stays_positiveb l = true.

Fixpoint q2253746_vote_sequences (n : nat) : list (list Z) :=
  match n with
  | O => [[]]
  | S k =>
      map (cons 1%Z) (q2253746_vote_sequences k) ++
      map (cons (-1)%Z) (q2253746_vote_sequences k)
  end.

Definition q2253746_counted_sequenceb
    (p q : nat) (l : list Z) : bool :=
  andb
    (Nat.eqb (count_occ Z.eq_dec l 1%Z) p)
    (andb
      (Nat.eqb (count_occ Z.eq_dec l (-1)%Z) q)
      (forallb
        (fun x => orb (Z.eqb x 1%Z) (Z.eqb x (-1)%Z))
        l)).

Definition q2253746_counted_sequence
    (p q : nat) (l : list Z) : Prop :=
  q2253746_counted_sequenceb p q l = true.

Definition q2253746_counted_sequences
    (p q : nat) : list (list Z) :=
  filter
    (q2253746_counted_sequenceb p q)
    (q2253746_vote_sequences (p + q)).

Definition q2253746_uniform_probability
    (p q : nat) : R :=
  (INR
      (length
        (filter
          q2253746_stays_positiveb
          (q2253746_counted_sequences p q))) /
    INR (length (q2253746_counted_sequences p q)))%R.

Theorem ballot_problem :
  forall q p : nat,
    (q < p)%nat ->
    q2253746_uniform_probability p q =
      (INR (p - q) / INR (p + q))%R.
Admitted.
