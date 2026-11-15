(* Statement-only formalization of VERINA corpus artifact verina_advanced_21,
   catalog title "isPalindrome": an executable Unicode-string palindrome test
   using both symmetric indexing and reversal, together with its correctness
   contract. This file contains no proof. *)

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

Definition isPalindrome_precond (_s : lean_string) : Prop :=
  True.

Fixpoint isPalindrome_checkIndices_fuel
    (fuel left right : nat)
    (chars : list lean_char) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if Nat.leb right left
      then true
      else
        match nth_error chars left, nth_error chars right with
        | Some cLeft, Some cRight =>
            if lean_char_eqb cLeft cRight
            then
              isPalindrome_checkIndices_fuel
                fuel' (S left) (Nat.pred right) chars
            else false
        | _, _ => false
        end
  end.

Definition isPalindrome_checkIndices
    (left right : nat)
    (chars : list lean_char) : bool :=
  isPalindrome_checkIndices_fuel (S right) left right chars.

Fixpoint isPalindrome_reverseList
    (acc xs : list lean_char) : list lean_char :=
  match xs with
  | [] => acc
  | x :: xs' => isPalindrome_reverseList (x :: acc) xs'
  end.

Definition isPalindrome
    (s : lean_string)
    (_h_precond : isPalindrome_precond s) : bool :=
  let length := List.length s in
  if Nat.leb length 1
  then true
  else
    let arr := s in
    let approach1 :=
      isPalindrome_checkIndices 0 (Nat.pred length) arr in
    let reversed := isPalindrome_reverseList [] arr in
    let approach2 := lean_char_list_eqb arr reversed in
    andb approach1 approach2.

Definition isPalindrome_postcond
    (s : lean_string)
    (result : bool)
    (_h_precond : isPalindrome_precond s) : Prop :=
  (result = true ->
    lean_char_list_eqb s (rev s) = true) /\
  (result = false ->
    s <> [] /\ negb (lean_char_list_eqb s (rev s)) = true).

Theorem isPalindrome_spec_satisfied
    (s : lean_string)
    (h_precond : isPalindrome_precond s) :
  isPalindrome_postcond
    s (isPalindrome s h_precond) h_precond.
Admitted.
