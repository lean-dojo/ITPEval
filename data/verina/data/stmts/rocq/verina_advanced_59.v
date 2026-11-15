(* Statement-only formalization of VERINA corpus artifact verina_advanced_59,
   catalog title "palindromeIgnoreNonAlnum": an executable Unicode-string
   palindrome test that ignores non-ASCII-alphanumeric characters and ASCII
   case differences, together with its correctness contract. This file
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

Definition palindrome_isUpperAlpha (c : lean_char) : bool :=
  match c with
  | LeanAscii a =>
      andb
        (Nat.leb 65 (Ascii.nat_of_ascii a))
        (Nat.leb (Ascii.nat_of_ascii a) 90)
  | LeanNonAscii _ _ _ => false
  end.

Definition palindrome_isLowerAlpha (c : lean_char) : bool :=
  match c with
  | LeanAscii a =>
      andb
        (Nat.leb 97 (Ascii.nat_of_ascii a))
        (Nat.leb (Ascii.nat_of_ascii a) 122)
  | LeanNonAscii _ _ _ => false
  end.

Definition palindrome_isAlpha (c : lean_char) : bool :=
  orb (palindrome_isUpperAlpha c) (palindrome_isLowerAlpha c).

Definition palindrome_isDigit (c : lean_char) : bool :=
  match c with
  | LeanAscii a =>
      andb
        (Nat.leb 48 (Ascii.nat_of_ascii a))
        (Nat.leb (Ascii.nat_of_ascii a) 57)
  | LeanNonAscii _ _ _ => false
  end.

Definition palindrome_toLower (c : lean_char) : lean_char :=
  match c with
  | LeanAscii a =>
      if palindrome_isUpperAlpha (LeanAscii a)
      then
        LeanAscii
          (Ascii.ascii_of_nat (Ascii.nat_of_ascii a + 32))
      else LeanAscii a
  | LeanNonAscii code hlarge hvalid =>
      LeanNonAscii code hlarge hvalid
  end.

Definition lean_char_eqb (x y : lean_char) : bool :=
  match x, y with
  | LeanAscii a, LeanAscii b =>
      Nat.eqb (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
  | LeanNonAscii xcode _ _, LeanNonAscii ycode _ _ =>
      N.eqb xcode ycode
  | _, _ => false
  end.

Definition lean_char_option_eqb
    (x y : option lean_char) : bool :=
  match x, y with
  | None, None => true
  | Some x', Some y' => lean_char_eqb x' y'
  | _, _ => false
  end.

Definition palindromeIgnoreNonAlnum_clean
    (s : lean_string) : list lean_char :=
  map palindrome_toLower
    (filter
      (fun c => orb (palindrome_isAlpha c) (palindrome_isDigit c))
      s).

Definition palindromeIgnoreNonAlnum_precond
    (_s : lean_string) : Prop :=
  True.

Fixpoint palindromeIgnoreNonAlnum_check_fuel
    (fuel left right : nat)
    (cleaned : list lean_char) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
      if Nat.leb right left
      then true
      else if lean_char_option_eqb
                (nth_error cleaned left)
                (nth_error cleaned right)
           then
             palindromeIgnoreNonAlnum_check_fuel
               fuel' (S left) (Nat.pred right) cleaned
           else false
  end.

Definition palindromeIgnoreNonAlnum
    (s : lean_string)
    (_h_precond : palindromeIgnoreNonAlnum_precond s) : bool :=
  let cleaned := palindromeIgnoreNonAlnum_clean s in
  let n := length cleaned in
  palindromeIgnoreNonAlnum_check_fuel
    n 0 (Nat.pred n) cleaned.

Definition palindromeIgnoreNonAlnum_postcond
    (s : lean_string)
    (result : bool)
    (_h_precond : palindromeIgnoreNonAlnum_precond s) : Prop :=
  let cleaned := palindromeIgnoreNonAlnum_clean s in
  let forward := cleaned in
  let backward := rev cleaned in
  if result
  then forward = backward
  else forward <> backward.

Theorem palindromeIgnoreNonAlnum_spec_satisfied
    (s : lean_string)
    (h_precond : palindromeIgnoreNonAlnum_precond s) :
  palindromeIgnoreNonAlnum_postcond
    s (palindromeIgnoreNonAlnum s h_precond) h_precond.
Admitted.
