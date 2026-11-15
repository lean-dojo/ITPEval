(* Statement-only formalization of VERINA corpus artifact verina_advanced_6,
   catalog title "allVowels": an executable case-insensitive ASCII-vowel
   containment test over Unicode strings, together with its correctness
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

Definition allVowels_isUpperAscii (c : lean_char) : bool :=
  match c with
  | LeanAscii a =>
      andb
        (Nat.leb 65 (Ascii.nat_of_ascii a))
        (Nat.leb (Ascii.nat_of_ascii a) 90)
  | LeanNonAscii _ _ _ => false
  end.

Definition toLower (c : lean_char) : lean_char :=
  match c with
  | LeanAscii a =>
      if allVowels_isUpperAscii (LeanAscii a)
      then
        LeanAscii
          (Ascii.ascii_of_nat (Ascii.nat_of_ascii a + 32))
      else LeanAscii a
  | LeanNonAscii code hlarge hvalid =>
      LeanNonAscii code hlarge hvalid
  end.

Definition normalize_str (s : lean_string) : list lean_char :=
  map toLower s.

Definition lean_char_eqb (x y : lean_char) : bool :=
  match x, y with
  | LeanAscii a, LeanAscii b =>
      Nat.eqb (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
  | LeanNonAscii xcode _ _, LeanNonAscii ycode _ _ =>
      N.eqb xcode ycode
  | _, _ => false
  end.

Definition allVowels_ascii_char (code : nat) : lean_char :=
  LeanAscii (Ascii.ascii_of_nat code).

Definition allVowels_vowelSet : list lean_char :=
  [allVowels_ascii_char 97;
   allVowels_ascii_char 101;
   allVowels_ascii_char 105;
   allVowels_ascii_char 111;
   allVowels_ascii_char 117].

Definition allVowels_contains
    (v : lean_char) (chars : list lean_char) : bool :=
  existsb (fun c => lean_char_eqb c v) chars.

Definition allVowels_precond (_s : lean_string) : Prop :=
  True.

Definition allVowels
    (s : lean_string)
    (_h_precond : allVowels_precond s) : bool :=
  let chars := normalize_str s in
  forallb
    (fun v => allVowels_contains v chars)
    allVowels_vowelSet.

Definition allVowels_postcond
    (s : lean_string)
    (result : bool)
    (_h_precond : allVowels_precond s) : Prop :=
  let chars := normalize_str s in
  result = true <->
  forallb
    (fun v => allVowels_contains v chars)
    allVowels_vowelSet = true.

Theorem allVowels_spec_satisfied
    (s : lean_string)
    (h_precond : allVowels_precond s) :
  allVowels_postcond
    s (allVowels s h_precond) h_precond.
Admitted.
