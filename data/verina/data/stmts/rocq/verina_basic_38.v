(* Statement-only formalization of VERINA corpus artifact verina_basic_38,
   catalog title "allCharactersSame": an executable Boolean test that an
   arbitrary Unicode string is empty or has every character equal to its
   first character, together with its correctness contract. This file
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

Definition lean_char_scalar_value (c : lean_char) : N :=
  match c with
  | LeanAscii a => N.of_nat (Ascii.nat_of_ascii a)
  | LeanNonAscii code _ _ => code
  end.

Definition allCharactersSame_default_char : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 0).

Definition allCharactersSame_precond (_s : lean_string) : Prop :=
  True.

Fixpoint allCharactersSame_all_eq
    (first : lean_char) (rest : list lean_char) : bool :=
  match rest with
  | [] => true
  | x :: xs =>
      andb
        (lean_char_eqb x first)
        (allCharactersSame_all_eq first xs)
  end.

Definition allCharactersSame
    (s : lean_string)
    (_h_precond : allCharactersSame_precond s) : bool :=
  match s with
  | [] => true
  | first :: rest => allCharactersSame_all_eq first rest
  end.

Fixpoint allCharactersSame_pairwise_eq
    (chars : list lean_char) : Prop :=
  match chars with
  | [] => True
  | first :: rest =>
      Forall
        (fun x =>
          lean_char_scalar_value first =
          lean_char_scalar_value x)
        rest /\
      allCharactersSame_pairwise_eq rest
  end.

Definition allCharactersSame_has_difference_from_first
    (chars : list lean_char) : bool :=
  existsb
    (fun x =>
      negb
        (lean_char_eqb
          x
          (nth 0 chars allCharactersSame_default_char)))
    chars.

Definition allCharactersSame_postcond
    (s : lean_string)
    (result : bool)
    (_h_precond : allCharactersSame_precond s) : Prop :=
  (result = true ->
    allCharactersSame_pairwise_eq s) /\
  (result = false ->
    s <> [] /\
    allCharactersSame_has_difference_from_first s = true).

Theorem allCharactersSame_spec_satisfied
    (s : lean_string)
    (h_precond : allCharactersSame_precond s) :
  allCharactersSame_postcond
    s (allCharactersSame s h_precond) h_precond.
Admitted.
