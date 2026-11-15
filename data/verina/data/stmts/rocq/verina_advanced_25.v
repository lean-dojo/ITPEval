(* Statement-only formalization of VERINA corpus artifact verina_advanced_25,
   catalog title "lengthOfLIS": an executable dynamic-programming computation
   of the longest strictly increasing subsequence length of an integer list,
   together with its exhaustive-subsequence maximality contract. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition lengthOfLIS_precond (_nums : list Z) : Prop :=
  True.

Definition lengthOfLIS_get_Z
    (xs : list Z) (index : nat) : Z :=
  nth index xs 0%Z.

Definition lengthOfLIS_get_nat
    (xs : list nat) (index : nat) : nat :=
  nth index xs 0%nat.

Fixpoint lengthOfLIS_set_nat
    (index value : nat) (xs : list nat) : list nat :=
  match index, xs with
  | 0%nat, _ :: rest => value :: rest
  | S index', x :: rest =>
      x :: lengthOfLIS_set_nat index' value rest
  | _, [] => []
  end.

Definition maxInArray (arr : list nat) : nat :=
  fold_left
    (fun a b => if Nat.leb b a then a else b)
    arr 0%nat.

Definition lengthOfLIS_cell
    (nums : list Z)
    (i : nat)
    (dp : list nat)
    (j : nat) : list nat :=
  if andb
       (Z.ltb
         (lengthOfLIS_get_Z nums j)
         (lengthOfLIS_get_Z nums i))
       (Nat.ltb
         (lengthOfLIS_get_nat dp i)
         (S (lengthOfLIS_get_nat dp j)))
  then
    lengthOfLIS_set_nat
      i (S (lengthOfLIS_get_nat dp j)) dp
  else dp.

Definition lengthOfLIS_row
    (nums : list Z)
    (dp : list nat)
    (i : nat) : list nat :=
  fold_left
    (lengthOfLIS_cell nums i)
    (seq 0%nat i)
    dp.

Definition lengthOfLIS
    (nums : list Z)
    (_h_precond : lengthOfLIS_precond nums) : nat :=
  match nums with
  | [] => 0%nat
  | _ =>
      let n := length nums in
      let initial := repeat 1%nat n in
      let dp :=
        fold_left
          (lengthOfLIS_row nums)
          (seq 1%nat (Nat.pred n))
          initial in
      maxInArray dp
  end.

Definition lengthOfLIS_allSubseq
    (nums : list Z) : list (list Z) :=
  map
    (fun sub : list Z => rev sub)
    (fold_left
      (fun acc x =>
        acc ++ map (fun sub => x :: sub) acc)
      nums [[]]).

Fixpoint lengthOfLIS_pairwiseLess
    (xs : list Z) : bool :=
  match xs with
  | [] => true
  | x :: rest =>
      andb
        (forallb (fun y => Z.ltb x y) rest)
        (lengthOfLIS_pairwiseLess rest)
  end.

Definition lengthOfLIS_postcond
    (nums : list Z)
    (result : nat)
    (_h_precond : lengthOfLIS_precond nums) : Prop :=
  let allSubseq := lengthOfLIS_allSubseq nums in
  let increasingSubseqLens :=
    map
      (fun xs : list Z => length xs)
      (filter lengthOfLIS_pairwiseLess allSubseq) in
  existsb (Nat.eqb result) increasingSubseqLens = true /\
  forallb (fun candidate => Nat.leb candidate result)
    increasingSubseqLens = true.

Theorem lengthOfLIS_spec_satisfied
    (nums : list Z)
    (h_precond : lengthOfLIS_precond nums) :
  lengthOfLIS_postcond
    nums (lengthOfLIS nums h_precond) h_precond.
Admitted.
