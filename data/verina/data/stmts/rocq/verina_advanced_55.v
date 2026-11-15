(* Statement-only formalization of VERINA corpus artifact verina_advanced_55,
   catalog title "mostFrequent": an executable frequency-map computation that
   returns a maximum-frequency integer, breaking ties by its first occurrence
   in the original nonempty list, together with its correctness contract.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition mostFrequent_precond (xs : list Z) : Prop :=
  xs <> [].

Definition mostFrequent_freq_map := list (Z * nat).

Fixpoint mostFrequent_map_get
    (key : Z)
    (m : mostFrequent_freq_map) : nat :=
  match m with
  | [] => 0%nat
  | (stored_key, value) :: rest =>
      if Z.eqb key stored_key
      then value
      else mostFrequent_map_get key rest
  end.

Fixpoint mostFrequent_map_insert
    (key : Z)
    (value : nat)
    (m : mostFrequent_freq_map) : mostFrequent_freq_map :=
  match m with
  | [] => [(key, value)]
  | (stored_key, stored_value) :: rest =>
      if Z.eqb key stored_key
      then (key, value) :: rest
      else
        (stored_key, stored_value) ::
        mostFrequent_map_insert key value rest
  end.

Definition countMap (xs : list Z) : mostFrequent_freq_map :=
  fold_left
    (fun m x =>
      let current := mostFrequent_map_get x m in
      mostFrequent_map_insert x (S current) m)
    xs [].

Definition getMaxFrequency
    (m : mostFrequent_freq_map) : nat :=
  fold_left
    (fun acc entry =>
      let value := snd entry in
      if Nat.ltb acc value then value else acc)
    m 0%nat.

Definition getCandidates
    (m : mostFrequent_freq_map)
    (maxFreq : nat) : list Z :=
  map fst
    (filter
      (fun entry => Nat.eqb (snd entry) maxFreq)
      m).

Fixpoint getFirstWithFreq
    (xs candidates : list Z) : Z :=
  match xs with
  | [] => 0%Z
  | x :: rest =>
      if existsb (Z.eqb x) candidates
      then x
      else getFirstWithFreq rest candidates
  end.

Definition mostFrequent
    (xs : list Z)
    (_h_precond : mostFrequent_precond xs) : Z :=
  let freqMap := countMap xs in
  let maxF := getMaxFrequency freqMap in
  let candidates := getCandidates freqMap maxF in
  getFirstWithFreq xs candidates.

Definition mostFrequent_postcond
    (xs : list Z)
    (result : Z)
    (_h_precond : mostFrequent_precond xs) : Prop :=
  let count := fun x => count_occ Z.eq_dec xs x in
  In result xs /\
  forallb
    (fun x => Nat.leb (count x) (count result))
    xs = true /\
  hd_error
    (filter
      (fun x => Nat.eqb (count x) (count result))
      xs) = Some result.

Theorem mostFrequent_spec_satisfied
    (xs : list Z)
    (h_precond : mostFrequent_precond xs) :
  mostFrequent_postcond
    xs (mostFrequent xs h_precond) h_precond.
Admitted.
