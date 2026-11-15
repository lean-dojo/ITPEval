(* Statement-only formalization of VERINA corpus artifact verina_advanced_2,
   catalog title "LongestCommonSubsequence": an executable dynamic-programming
   computation of the longest common subsequence length for two integer arrays,
   together with its exhaustive-subsequence correctness contract. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition LongestCommonSubsequence_precond
    (_a _b : list Z) : Prop :=
  True.

Definition intMax (x y : Z) : Z :=
  if Z.ltb x y then y else x.

Fixpoint lcs_set_nth {A : Type}
    (index : nat) (value : A) (xs : list A) : list A :=
  match index, xs with
  | 0%nat, _ :: rest => value :: rest
  | S index', x :: rest =>
      x :: lcs_set_nth index' value rest
  | _, [] => []
  end.

Definition lcs_get_row
    (dp : list (list Z)) (i : nat) : list Z :=
  nth i dp [].

Definition lcs_get_cell
    (dp : list (list Z)) (i j : nat) : Z :=
  nth j (lcs_get_row dp i) 0.

Definition lcs_update_cell
    (a b : list Z)
    (i j : nat)
    (dp : list (list Z)) : list (list Z) :=
  if orb (Nat.eqb i 0%nat) (Nat.eqb j 0%nat)
  then dp
  else
    let ai := nth (Nat.pred i) a 0 in
    let bj := nth (Nat.pred j) b 0 in
    let newVal :=
      if Z.eqb ai bj
      then lcs_get_cell dp (Nat.pred i) (Nat.pred j) + 1
      else
        intMax
          (lcs_get_cell dp (Nat.pred i) j)
          (lcs_get_cell dp i (Nat.pred j)) in
    let row := lcs_get_row dp i in
    lcs_set_nth i (lcs_set_nth j newVal row) dp.

Fixpoint lcs_run_columns
    (a b : list Z)
    (i remaining j : nat)
    (dp : list (list Z)) : list (list Z) :=
  match remaining with
  | 0%nat => dp
  | S remaining' =>
      lcs_run_columns
        a b i remaining' (S j)
        (lcs_update_cell a b i j dp)
  end.

Fixpoint lcs_run_rows
    (a b : list Z)
    (column_count remaining i : nat)
    (dp : list (list Z)) : list (list Z) :=
  match remaining with
  | 0%nat => dp
  | S remaining' =>
      let dp' := lcs_run_columns a b i column_count 0%nat dp in
      lcs_run_rows
        a b column_count remaining' (S i) dp'
  end.

Definition LongestCommonSubsequence
    (a b : list Z)
    (_h_precond : LongestCommonSubsequence_precond a b) : Z :=
  let m := length a in
  let n := length b in
  let dp0 := repeat (repeat 0 (S n)) (S m) in
  let dp :=
    lcs_run_rows a b (S n) (S m) 0%nat dp0 in
  lcs_get_cell dp m n.

Definition lcs_allSubseq (arr : list Z) : list (list Z) :=
  map
    (fun sub : list Z => rev sub)
    (fold_left
      (fun acc x =>
        acc ++ map (fun sub => x :: sub) acc)
      arr [[]]).

Fixpoint lcs_list_Z_eqb
    (xs ys : list Z) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      andb (Z.eqb x y) (lcs_list_Z_eqb xs' ys')
  | _, _ => false
  end.

Definition lcs_contains_subsequence
    (needle : list Z) (haystack : list (list Z)) : bool :=
  existsb (fun candidate => lcs_list_Z_eqb candidate needle) haystack.

Definition lcs_contains_length
    (needle : Z) (haystack : list Z) : bool :=
  existsb (fun candidate => Z.eqb candidate needle) haystack.

Definition LongestCommonSubsequence_postcond
    (a b : list Z)
    (result : Z)
    (_h_precond : LongestCommonSubsequence_precond a b) : Prop :=
  let subseqA := lcs_allSubseq a in
  let subseqB := lcs_allSubseq b in
  let commonSubseqLens :=
    map
      (fun sub : list Z => Z.of_nat (length sub))
      (filter
        (fun sub => lcs_contains_subsequence sub subseqB)
        subseqA) in
  lcs_contains_length result commonSubseqLens = true /\
  forallb (fun candidate => Z.leb candidate result) commonSubseqLens = true.

Theorem LongestCommonSubsequence_spec_satisfied
    (a b : list Z)
    (h_precond : LongestCommonSubsequence_precond a b) :
  LongestCommonSubsequence_postcond
    a b (LongestCommonSubsequence a b h_precond) h_precond.
Admitted.
