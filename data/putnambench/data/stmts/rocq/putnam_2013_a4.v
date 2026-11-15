(* Statement-only formalization of PutnamBench corpus artifact putnam_2013_a4:
   balanced zero counts on equal-length arcs of a finite binary circle force
   an arc realizing integral average zero and one counts. This file contains
   no proof. *)

From Stdlib Require Import Arith.PeanoNat ZArith.

Inductive putnam_2013_a4_digit : Type :=
  | putnam_2013_a4_zero
  | putnam_2013_a4_one.

Definition putnam_2013_a4_digit_eqb
    (a b : putnam_2013_a4_digit) : bool :=
  match a, b with
  | putnam_2013_a4_zero, putnam_2013_a4_zero => true
  | putnam_2013_a4_one, putnam_2013_a4_one => true
  | _, _ => false
  end.

Definition putnam_2013_a4_index (n : nat) : Type :=
  {i : nat | (i < n)%nat}.

Definition putnam_2013_a4_length (n : nat) : Type :=
  {l : nat | (l <= n)%nat}.

Definition putnam_2013_a4_arc (n : nat) : Type :=
  (putnam_2013_a4_index n * putnam_2013_a4_length n)%type.

Definition putnam_2013_a4_cyclic_index
    (n : nat)
    (npos : (0 < n)%nat)
    (start : putnam_2013_a4_index n)
    (offset : nat) : putnam_2013_a4_index n :=
  exist
    (fun i : nat => (i < n)%nat)
    ((proj1_sig start + offset) mod n)
    (Nat.mod_upper_bound
      (proj1_sig start + offset)
      n
      (proj2 (Nat.neq_0_lt_0 n) npos)).

Fixpoint putnam_2013_a4_count_digit
    (n : nat)
    (npos : (0 < n)%nat)
    (circle : putnam_2013_a4_index n -> putnam_2013_a4_digit)
    (start : putnam_2013_a4_index n)
    (target : putnam_2013_a4_digit)
    (length : nat) : Z :=
  match length with
  | O => 0%Z
  | S l =>
      (putnam_2013_a4_count_digit n npos circle start target l +
       if putnam_2013_a4_digit_eqb
            (circle (putnam_2013_a4_cyclic_index n npos start l))
            target
       then 1
       else 0)%Z
  end.

Definition putnam_2013_a4_zero_count
    (n : nat)
    (npos : (0 < n)%nat)
    (circle : putnam_2013_a4_index n -> putnam_2013_a4_digit)
    (w : putnam_2013_a4_arc n) : Z :=
  putnam_2013_a4_count_digit
    n npos circle (fst w) putnam_2013_a4_zero (proj1_sig (snd w)).

Definition putnam_2013_a4_one_count
    (n : nat)
    (npos : (0 < n)%nat)
    (circle : putnam_2013_a4_index n -> putnam_2013_a4_digit)
    (w : putnam_2013_a4_arc n) : Z :=
  putnam_2013_a4_count_digit
    n npos circle (fst w) putnam_2013_a4_one (proj1_sig (snd w)).

Fixpoint putnam_2013_a4_fin_sum
    (n : nat) : (putnam_2013_a4_index n -> Z) -> Z :=
  match n as m return (putnam_2013_a4_index m -> Z) -> Z with
  | O => fun _ => 0%Z
  | S m =>
      fun f =>
        (f (exist
              (fun i : nat => (i < S m)%nat)
              O
              (Nat.lt_0_succ m)) +
         putnam_2013_a4_fin_sum m
           (fun i =>
              f (exist
                   (fun j : nat => (j < S m)%nat)
                   (S (proj1_sig i))
                   (proj1
                     (Nat.succ_lt_mono (proj1_sig i) m)
                     (proj2_sig i)))))%Z
  end.

Theorem putnam_2013_a4
    (n k : nat)
    (circle : putnam_2013_a4_index n -> putnam_2013_a4_digit)
    (ws : putnam_2013_a4_index k -> putnam_2013_a4_arc n)
    (Zsum Nsum : Z)
    (npos : (0 < n)%nat)
    (kpos : (0 < k)%nat)
    (Zle1 :
      forall w w' : putnam_2013_a4_arc n,
        proj1_sig (snd w) = proj1_sig (snd w') ->
        (Z.abs
          (putnam_2013_a4_zero_count n npos circle w -
           putnam_2013_a4_zero_count n npos circle w') <= 1)%Z)
    (hZsum :
      (Z.of_nat k * Zsum =
       putnam_2013_a4_fin_sum k
         (fun j => putnam_2013_a4_zero_count n npos circle (ws j)))%Z)
    (hNsum :
      (Z.of_nat k * Nsum =
       putnam_2013_a4_fin_sum k
         (fun j => putnam_2013_a4_one_count n npos circle (ws j)))%Z) :
  exists w : putnam_2013_a4_arc n,
    putnam_2013_a4_zero_count n npos circle w = Zsum /\
    putnam_2013_a4_one_count n npos circle w = Nsum.
Admitted.
