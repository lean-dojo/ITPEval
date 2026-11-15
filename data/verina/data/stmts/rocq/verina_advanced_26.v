(* Statement-only formalization of VERINA corpus artifact verina_advanced_26,
   catalog title "letterCombinations": the executable generation of telephone
   keypad letter combinations for a Unicode string, with empty or invalid
   inputs rejected, together with its correctness contract. This file
   contains no proof. *)

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

Fixpoint lean_string_eqb
    (xs ys : lean_string) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      andb (lean_char_eqb x y) (lean_string_eqb xs' ys')
  | _, _ => false
  end.

Definition lean_ascii_char (code : nat) : lean_char :=
  LeanAscii (Ascii.ascii_of_nat code).

Definition digitToLetters (c : lean_char) : list lean_char :=
  match c with
  | LeanAscii a =>
      let code := Ascii.nat_of_ascii a in
      if Nat.eqb code 50 then
        [lean_ascii_char 97; lean_ascii_char 98; lean_ascii_char 99]
      else if Nat.eqb code 51 then
        [lean_ascii_char 100; lean_ascii_char 101; lean_ascii_char 102]
      else if Nat.eqb code 52 then
        [lean_ascii_char 103; lean_ascii_char 104; lean_ascii_char 105]
      else if Nat.eqb code 53 then
        [lean_ascii_char 106; lean_ascii_char 107; lean_ascii_char 108]
      else if Nat.eqb code 54 then
        [lean_ascii_char 109; lean_ascii_char 110; lean_ascii_char 111]
      else if Nat.eqb code 55 then
        [lean_ascii_char 112; lean_ascii_char 113;
         lean_ascii_char 114; lean_ascii_char 115]
      else if Nat.eqb code 56 then
        [lean_ascii_char 116; lean_ascii_char 117; lean_ascii_char 118]
      else if Nat.eqb code 57 then
        [lean_ascii_char 119; lean_ascii_char 120;
         lean_ascii_char 121; lean_ascii_char 122]
      else []
  | LeanNonAscii _ _ _ => []
  end.

Definition letterCombinations_precond
    (_digits : lean_string) : Prop :=
  True.

Fixpoint letterCombinations_go
    (chars : list lean_char) : list lean_string :=
  match chars with
  | [] => []
  | d :: ds =>
      let restCombinations := letterCombinations_go ds in
      let currentLetters := digitToLetters d in
      match restCombinations with
      | [] => map (fun c => [c]) currentLetters
      | _ =>
          flat_map
            (fun c =>
              map (fun s => [c] ++ s) restCombinations)
            currentLetters
      end
  end.

Definition letterCombinations
    (digits : lean_string)
    (_h_precond : letterCombinations_precond digits)
    : list lean_string :=
  if existsb
       (fun c => lean_string_eqb (digitToLetters c) [])
       digits
  then []
  else letterCombinations_go digits.

Definition letterCombinations_valid_digit
    (c : lean_char) : bool :=
  match c with
  | LeanAscii a =>
      let code := Ascii.nat_of_ascii a in
      orb (Nat.eqb code 50)
        (orb (Nat.eqb code 51)
          (orb (Nat.eqb code 52)
            (orb (Nat.eqb code 53)
              (orb (Nat.eqb code 54)
                (orb (Nat.eqb code 55)
                  (orb (Nat.eqb code 56)
                       (Nat.eqb code 57)))))))
  | LeanNonAscii _ _ _ => false
  end.

Definition letterCombinations_extend
    (acc : list lean_string)
    (letters : list lean_char) : list lean_string :=
  flat_map
    (fun s =>
      map (fun c => s ++ [c]) letters)
    acc.

Definition letterCombinations_expected
    (digits : lean_string) : list lean_string :=
  fold_left
    letterCombinations_extend
    (map digitToLetters digits)
    [[]].

Definition lean_string_mem
    (s : lean_string)
    (strings : list lean_string) : bool :=
  existsb (lean_string_eqb s) strings.

Definition letterCombinations_postcond
    (digits : lean_string)
    (result : list lean_string)
    (_h_precond : letterCombinations_precond digits) : Prop :=
  match digits with
  | [] => result = []
  | _ =>
      if existsb
           (fun c => negb (letterCombinations_valid_digit c))
           digits
      then result = []
      else
        let expected := letterCombinations_expected digits in
        length result = length expected /\
        forallb (fun s => lean_string_mem s expected) result = true /\
        forallb (fun s => lean_string_mem s result) expected = true
  end.

Theorem letterCombinations_spec_satisfied
    (digits : lean_string)
    (h_precond : letterCombinations_precond digits) :
  letterCombinations_postcond
    digits (letterCombinations digits h_precond) h_precond.
Admitted.
