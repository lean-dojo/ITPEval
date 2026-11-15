(* Statement-only formalization of VERINA corpus artifact verina_advanced_76,
   catalog title "topKFrequent": deterministic frequency counting and stable
   descending selection of the k most frequent integers, together with its
   membership, distinctness, frequency, and ordering correctness contract.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition topKFrequent_precond
    (nums : list Z) (k : nat) : Prop :=
  (k <= length (nodup Z.eq_dec nums))%nat.

Definition topKFrequent_find_key
    (n : Z)
    (frequencies : list (Z * nat)) : option (Z * nat) :=
  find (fun entry => Z.eqb (fst entry) n) frequencies.

Definition topKFrequent_increment_key
    (n : Z)
    (frequencies : list (Z * nat)) : list (Z * nat) :=
  map
    (fun entry =>
      let '(key, count) := entry in
      if Z.eqb key n
      then (key, S count)
      else (key, count))
    frequencies.

Definition topKFrequent_add_frequency
    (frequencies : list (Z * nat))
    (n : Z) : list (Z * nat) :=
  match topKFrequent_find_key n frequencies with
  | Some _ => topKFrequent_increment_key n frequencies
  | None => frequencies ++ [(n, 1%nat)]
  end.

Definition topKFrequent_frequency_list
    (nums : list Z) : list (Z * nat) :=
  fold_left topKFrequent_add_frequency nums [].

Fixpoint topKFrequent_insert_sorted
    (entry : Z * nat)
    (frequencies : list (Z * nat)) : list (Z * nat) :=
  match frequencies with
  | [] => [entry]
  | current :: rest =>
      if Nat.ltb (snd current) (snd entry)
      then entry :: current :: rest
      else current :: topKFrequent_insert_sorted entry rest
  end.

Definition topKFrequent_sorted_frequencies
    (nums : list Z) : list (Z * nat) :=
  fold_left
    (fun acc entry => topKFrequent_insert_sorted entry acc)
    (topKFrequent_frequency_list nums)
    [].

Definition topKFrequent
    (nums : list Z)
    (k : nat)
    (_h_precond : topKFrequent_precond nums k) : list Z :=
  map fst (firstn k (topKFrequent_sorted_frequencies nums)).

Fixpoint topKFrequent_pairwise
    {A : Type}
    (relation : A -> A -> Prop)
    (xs : list A) : Prop :=
  match xs with
  | [] => True
  | x :: rest =>
      Forall (relation x) rest /\
      topKFrequent_pairwise relation rest
  end.

Fixpoint topKFrequent_zipIdxFrom
    (xs : list Z)
    (index : nat) : list (Z * nat) :=
  match xs with
  | [] => []
  | x :: rest =>
      (x, index) :: topKFrequent_zipIdxFrom rest (S index)
  end.

Definition topKFrequent_zipIdx
    (xs : list Z) : list (Z * nat) :=
  topKFrequent_zipIdxFrom xs 0%nat.

Definition topKFrequent_mem
    (x : Z) (xs : list Z) : bool :=
  existsb (Z.eqb x) xs.

Definition topKFrequent_count
    (x : Z) (xs : list Z) : nat :=
  count_occ Z.eq_dec xs x.

Definition topKFrequent_postcond
    (nums : list Z)
    (k : nat)
    (result : list Z)
    (_h_precond : topKFrequent_precond nums k) : Prop :=
  length result = k /\
  forallb (fun x => topKFrequent_mem x nums) result = true /\
  topKFrequent_pairwise (fun x y => x <> y) result /\
  forallb
    (fun x =>
      forallb
        (fun y =>
          orb
            (topKFrequent_mem y result)
            (Nat.leb
              (topKFrequent_count y nums)
              (topKFrequent_count x nums)))
        nums)
    result = true /\
  topKFrequent_pairwise
    (fun first later =>
      let '(x, i) := first in
      let '(y, j) := later in
      (i < j)%nat ->
      (topKFrequent_count y nums <=
       topKFrequent_count x nums)%nat)
    (topKFrequent_zipIdx result).

Theorem topKFrequent_spec_satisfied
    (nums : list Z)
    (k : nat)
    (h_precond : topKFrequent_precond nums k) :
  topKFrequent_postcond
    nums k (topKFrequent nums k h_precond) h_precond.
Admitted.
