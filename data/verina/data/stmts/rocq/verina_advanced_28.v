(* Statement-only formalization of VERINA corpus artifact verina_advanced_28,
   catalog title "longestConsecutive": an executable finite-set scan computing
   the longest consecutive-integer streak in a duplicate-free integer list,
   together with its exhaustive sorted-sublist maximality contract. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition longestConsecutive_precond (nums : list Z) : Prop :=
  NoDup nums.

Definition longestConsecutive_set_contains
    (set : list Z) (x : Z) : bool :=
  existsb (Z.eqb x) set.

Definition longestConsecutive_set_insert
    (x : Z) (set : list Z) : list Z :=
  if longestConsecutive_set_contains set x
  then set
  else x :: set.

Definition longestConsecutive_build_set
    (nums : list Z) : list Z :=
  fold_left
    (fun set x => longestConsecutive_set_insert x set)
    nums [].

Fixpoint longestConsecutive_extend
    (set : list Z)
    (fuel : nat)
    (current : Z)
    (runLength : nat) : nat :=
  match fuel with
  | 0%nat => runLength
  | S fuel' =>
      if longestConsecutive_set_contains set (current + 1)
      then
        longestConsecutive_extend
          set fuel' (current + 1) (S runLength)
      else runLength
  end.

Fixpoint longestConsecutive_scan
    (set : list Z)
    (successorFuel : nat)
    (remaining : list Z)
    (maxLength : nat) : nat :=
  match remaining with
  | [] => maxLength
  | x :: xs =>
      let nextMax :=
        if negb
             (longestConsecutive_set_contains set (x - 1))
        then
          Nat.max maxLength
            (longestConsecutive_extend
              set successorFuel x 1%nat)
        else maxLength in
      longestConsecutive_scan
        set successorFuel xs nextMax
  end.

Definition longestConsecutive
    (nums : list Z)
    (_h_precond : longestConsecutive_precond nums) : nat :=
  let set := longestConsecutive_build_set nums in
  longestConsecutive_scan set (length nums) nums 0%nat.

Fixpoint longestConsecutive_insert_sorted
    (x : Z) (xs : list Z) : list Z :=
  match xs with
  | [] => [x]
  | y :: ys =>
      if Z.leb x y
      then x :: y :: ys
      else y :: longestConsecutive_insert_sorted x ys
  end.

Fixpoint longestConsecutive_sort
    (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: rest =>
      longestConsecutive_insert_sorted
        x (longestConsecutive_sort rest)
  end.

Fixpoint longestConsecutive_zipIdxFrom
    (xs : list Z)
    (index : nat) : list (Z * nat) :=
  match xs with
  | [] => []
  | x :: rest =>
      (x, index) ::
      longestConsecutive_zipIdxFrom rest (S index)
  end.

Definition longestConsecutive_zipIdx
    (xs : list Z) : list (Z * nat) :=
  longestConsecutive_zipIdxFrom xs 0%nat.

Definition isConsecutive (xs : list Z) : bool :=
  let first := hd 0 xs in
  orb
    (Nat.eqb (length xs) 0%nat)
    (forallb
      (fun indexed =>
        Z.eqb
          (fst indexed)
          (Z.of_nat (snd indexed) + first))
      (longestConsecutive_zipIdx xs)).

Definition longestConsecutive_candidate_sublists
    (sorted_nums : list Z) : list (list Z) :=
  let n := length sorted_nums in
  flat_map
    (fun start =>
      map
        (fun len => firstn len (skipn start sorted_nums))
        (seq 0%nat (S (n - start))))
    (seq 0%nat n).

Definition longestConsecutive_postcond
    (nums : list Z)
    (result : nat)
    (_h_precond : longestConsecutive_precond nums) : Prop :=
  let sorted_nums := longestConsecutive_sort nums in
  let consec_sublist_lens :=
    map (fun xs : list Z => length xs)
      (filter isConsecutive
        (longestConsecutive_candidate_sublists sorted_nums)) in
  (nums = [] -> result = 0%nat) /\
  (nums <> [] ->
    existsb (Nat.eqb result) consec_sublist_lens = true /\
    forallb
      (fun candidate => Nat.leb candidate result)
      consec_sublist_lens = true).

Theorem longestConsecutive_spec_satisfied
    (nums : list Z)
    (h_precond : longestConsecutive_precond nums) :
  longestConsecutive_postcond
    nums (longestConsecutive nums h_precond) h_precond.
Admitted.
