(* Statement-only formalization of VERINA corpus artifact verina_advanced_19,
   catalog title "isCleanPalindrome": an executable Unicode-string palindrome
   test that filters non-ASCII letters and lowercases ASCII uppercase letters,
   together with its correctness contract. This file contains no proof. *)

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

Definition isUpperAlpha (c : lean_char) : bool :=
  match c with
  | LeanAscii a =>
      andb
        (Nat.leb 65 (Ascii.nat_of_ascii a))
        (Nat.leb (Ascii.nat_of_ascii a) 90)
  | LeanNonAscii _ _ _ => false
  end.

Definition isLowerAlpha (c : lean_char) : bool :=
  match c with
  | LeanAscii a =>
      andb
        (Nat.leb 97 (Ascii.nat_of_ascii a))
        (Nat.leb (Ascii.nat_of_ascii a) 122)
  | LeanNonAscii _ _ _ => false
  end.

Definition isAlpha (c : lean_char) : bool :=
  orb (isUpperAlpha c) (isLowerAlpha c).

Definition toLower (c : lean_char) : lean_char :=
  match c with
  | LeanAscii a =>
      if isUpperAlpha (LeanAscii a)
      then
        LeanAscii
          (Ascii.ascii_of_nat (Ascii.nat_of_ascii a + 32))
      else LeanAscii a
  | LeanNonAscii code hlarge hvalid =>
      LeanNonAscii code hlarge hvalid
  end.

Definition normalizeChar (c : lean_char) : option lean_char :=
  if isAlpha c then Some (toLower c) else None.

Definition normalizeString (s : lean_string) : list lean_char :=
  fold_right
    (fun c acc =>
      match normalizeChar c with
      | Some c' => c' :: acc
      | None => acc
      end)
    [] s.

Definition isCleanPalindrome_precond (_s : lean_string) : Prop :=
  True.

Definition reverseList (xs : list lean_char) : list lean_char :=
  rev xs.

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

Definition isCleanPalindrome
    (s : lean_string)
    (_h_precond : isCleanPalindrome_precond s) : bool :=
  let norm := normalizeString s in
  lean_char_list_eqb norm (reverseList norm).

Definition isCleanPalindrome_postcond
    (s : lean_string)
    (result : bool)
    (_h_precond : isCleanPalindrome_precond s) : Prop :=
  let norm := normalizeString s in
  (result = true -> norm = rev norm) /\
  (result = false -> norm <> rev norm).

Theorem isCleanPalindrome_spec_satisfied
    (s : lean_string)
    (h_precond : isCleanPalindrome_precond s) :
  isCleanPalindrome_postcond
    s (isCleanPalindrome s h_precond) h_precond.
Admitted.
