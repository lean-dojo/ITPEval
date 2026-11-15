(* Statement-only formalization of VERINA corpus artifact verina_advanced_29,
   catalog title "longestGoodSubarray": an executable sliding-window
   computation of the longest natural-number subarray whose element
   frequencies are at most a positive bound, together with its exhaustive
   contiguous-subarray maximality contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Definition longestGoodSubarray_precond
    (_nums : list nat) (k : nat) : Prop :=
  0 < k.

Definition longestGoodSubarray_freq := list (nat * nat).

Fixpoint longestGoodSubarray_freq_get
    (key : nat)
    (freq : longestGoodSubarray_freq) : nat :=
  match freq with
  | [] => 0
  | (stored_key, value) :: rest =>
      if Nat.eqb key stored_key
      then value
      else longestGoodSubarray_freq_get key rest
  end.

Fixpoint longestGoodSubarray_freq_insert
    (key value : nat)
    (freq : longestGoodSubarray_freq)
    : longestGoodSubarray_freq :=
  match freq with
  | [] => [(key, value)]
  | (stored_key, stored_value) :: rest =>
      if Nat.eqb key stored_key
      then (key, value) :: rest
      else
        (stored_key, stored_value) ::
        longestGoodSubarray_freq_insert key value rest
  end.

Fixpoint longestGoodSubarray_freq_erase
    (key : nat)
    (freq : longestGoodSubarray_freq)
    : longestGoodSubarray_freq :=
  match freq with
  | [] => []
  | (stored_key, value) :: rest =>
      if Nat.eqb key stored_key
      then rest
      else
        (stored_key, value) ::
        longestGoodSubarray_freq_erase key rest
  end.

Definition longestGoodSubarray_freq_has_excess
    (k : nat)
    (freq : longestGoodSubarray_freq) : bool :=
  existsb
    (fun entry => Nat.ltb k (snd entry))
    freq.

Fixpoint longestGoodSubarray_shrink
    (nums : list nat)
    (k fuel left : nat)
    (freq : longestGoodSubarray_freq)
    : nat * longestGoodSubarray_freq :=
  match fuel with
  | 0 => (left, freq)
  | S fuel' =>
      if longestGoodSubarray_freq_has_excess k freq
      then
        let left_num := nth left nums 0 in
        let left_count :=
          longestGoodSubarray_freq_get left_num freq in
        let next_freq :=
          if Nat.eqb left_count 1
          then longestGoodSubarray_freq_erase left_num freq
          else
            longestGoodSubarray_freq_insert
              left_num (left_count - 1) freq in
        longestGoodSubarray_shrink
          nums k fuel' (S left) next_freq
      else (left, freq)
  end.

Fixpoint longestGoodSubarray_scan
    (nums : list nat)
    (k : nat)
    (remaining : list nat)
    (right left : nat)
    (freq : longestGoodSubarray_freq)
    (max_len : nat) : nat :=
  match remaining with
  | [] => max_len
  | num :: rest =>
      let count :=
        longestGoodSubarray_freq_get num freq in
      let inserted :=
        longestGoodSubarray_freq_insert num (count + 1) freq in
      let shrunk :=
        longestGoodSubarray_shrink
          nums k (length nums) left inserted in
      let next_left := fst shrunk in
      let next_freq := snd shrunk in
      let next_max :=
        Nat.max max_len (right - next_left + 1) in
      longestGoodSubarray_scan
        nums k rest (S right) next_left next_freq next_max
  end.

Definition longestGoodSubarray
    (nums : list nat)
    (k : nat)
    (_h_precond : longestGoodSubarray_precond nums k) : nat :=
  longestGoodSubarray_scan nums k nums 0 0 [] 0.

Definition longestGoodSubarray_subarrays
    (nums : list nat) : list (list nat) :=
  let n := length nums in
  flat_map
    (fun start =>
      map
        (fun len => firstn len (skipn start nums))
        (seq 0 (n - start + 1)))
    (seq 0 (n + 1)).

Definition longestGoodSubarray_subarray_freqs
    (subarrays : list (list nat)) : list (list nat) :=
  map
    (fun arr =>
      map
        (fun x => count_occ Nat.eq_dec arr x)
        arr)
    subarrays.

Definition longestGoodSubarray_valid_freqs
    (k : nat)
    (subarray_freqs : list (list nat)) : list (list nat) :=
  filter
    (fun arr => forallb (fun x => Nat.leb x k) arr)
    subarray_freqs.

Definition longestGoodSubarray_postcond
    (nums : list nat)
    (k result : nat)
    (_h_precond : longestGoodSubarray_precond nums k) : Prop :=
  let subarrays := longestGoodSubarray_subarrays nums in
  let subarray_freqs :=
    longestGoodSubarray_subarray_freqs subarrays in
  let valid_subarrays :=
    longestGoodSubarray_valid_freqs k subarray_freqs in
  (nums = [] /\ result = 0) \/
  (nums <> [] /\
    existsb
      (fun arr => Nat.eqb (length arr) result)
      valid_subarrays = true /\
    forallb
      (fun arr => Nat.leb (length arr) result)
      valid_subarrays = true).

Theorem longestGoodSubarray_spec_satisfied
    (nums : list nat)
    (k : nat)
    (h_precond : longestGoodSubarray_precond nums k) :
  longestGoodSubarray_postcond
    nums k (longestGoodSubarray nums k h_precond) h_precond.
Admitted.
