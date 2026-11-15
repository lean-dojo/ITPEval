(* Statement-only formalization of VERINA corpus artifact verina_advanced_27,
   catalog title "longestCommonSubsequence": the executable computation of a
   longest common subsequence of two Unicode strings, together with its
   exhaustive-subsequence maximality contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List NArith Strings.Ascii.

Import ListNotations.

Definition unicode_scalar (code : N) : Prop :=
  (code < 55296)%N \/
  ((57343 < code)%N /\ (code < 1114112)%N).

Inductive lean_char : Type :=
| LeanAscii : ascii -> lean_char
| LeanNonAscii :
    forall code : N,
      (256 <= code)%N ->
      unicode_scalar code ->
      lean_char.

Definition lean_string := list lean_char.

Definition lean_char_eqb (x y : lean_char) : bool :=
  match x, y with
  | LeanAscii a, LeanAscii b =>
      Nat.eqb (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
  | LeanNonAscii xcode _ _, LeanNonAscii ycode _ _ =>
      N.eqb xcode ycode
  | _, _ => false
  end.

Fixpoint lean_char_list_eqb
    (xs ys : list lean_char) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      andb (lean_char_eqb x y) (lean_char_list_eqb xs' ys')
  | _, _ => false
  end.

Definition longestCommonSubsequence_precond
    (_s1 _s2 : lean_string) : Prop :=
  True.

Definition toCharList (s : lean_string) : list lean_char :=
  s.

Definition fromCharList (cs : list lean_char) : lean_string :=
  fold_left (fun acc c => acc ++ [c]) cs [].

Fixpoint lcsAux_fuel
    (fuel : nat)
    (xs ys : list lean_char) : list lean_char :=
  match fuel with
  | 0%nat => []
  | S fuel' =>
      match xs, ys with
      | [], _ => []
      | _, [] => []
      | x :: xs', y :: ys' =>
          if lean_char_eqb x y
          then x :: lcsAux_fuel fuel' xs' ys'
          else
            let left := lcsAux_fuel fuel' xs' (y :: ys') in
            let right := lcsAux_fuel fuel' (x :: xs') ys' in
            if Nat.leb (length right) (length left)
            then left
            else right
      end
  end.

Definition lcsAux
    (xs ys : list lean_char) : list lean_char :=
  lcsAux_fuel (length xs + length ys) xs ys.

Definition longestCommonSubsequence
    (s1 s2 : lean_string)
    (_h_precond : longestCommonSubsequence_precond s1 s2)
    : lean_string :=
  let xs := toCharList s1 in
  let ys := toCharList s2 in
  let resultList := lcsAux xs ys in
  fromCharList resultList.

Definition lcs_allSubseq
    (arr : list lean_char) : list (list lean_char) :=
  map
    (fun sub : list lean_char => rev sub)
    (fold_left
      (fun acc x =>
        acc ++ map (fun sub => x :: sub) acc)
      arr [[]]).

Definition lcs_contains_subsequence
    (needle : list lean_char)
    (haystack : list (list lean_char)) : bool :=
  existsb
    (fun candidate => lean_char_list_eqb candidate needle)
    haystack.

Definition longestCommonSubsequence_postcond
    (s1 s2 : lean_string)
    (result : lean_string)
    (_h_precond : longestCommonSubsequence_precond s1 s2) : Prop :=
  let subseqA := lcs_allSubseq s1 in
  let subseqB := lcs_allSubseq s2 in
  let commonSubseq :=
    filter
      (fun candidate => lcs_contains_subsequence candidate subseqB)
      subseqA in
  lcs_contains_subsequence result commonSubseq = true /\
  forallb
    (fun candidate => Nat.leb (length candidate) (length result))
    commonSubseq = true.

Theorem longestCommonSubsequence_spec_satisfied
    (s1 s2 : lean_string)
    (h_precond : longestCommonSubsequence_precond s1 s2) :
  longestCommonSubsequence_postcond
    s1 s2 (longestCommonSubsequence s1 s2 h_precond) h_precond.
Admitted.
