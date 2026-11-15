(* Statement-only formalization of VERINA corpus artifact verina_basic_27,
   catalog title "findFirstRepeatedChar": an executable left-to-right scan of
   a Unicode string returns the first character encountered for a second time,
   together with its pairwise-distinct-prefix postcondition and final
   correctness proposition. This file contains no proof. *)

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

Definition findFirstRepeatedChar_precond
    (_s : lean_string) : Prop :=
  True.

Fixpoint findFirstRepeatedChar_loop
    (remaining seen : list lean_char) : option lean_char :=
  match remaining with
  | [] => None
  | c :: rest =>
      if existsb (fun prior => lean_char_eqb prior c) seen
      then Some c
      else findFirstRepeatedChar_loop rest (c :: seen)
  end.

Definition findFirstRepeatedChar
    (s : lean_string)
    (_h_precond : findFirstRepeatedChar_precond s)
    : option lean_char :=
  findFirstRepeatedChar_loop s [].

Fixpoint findFirstRepeatedChar_count
    (c : lean_char) (chars : list lean_char) : nat :=
  match chars with
  | [] => 0%nat
  | x :: rest =>
      if lean_char_eqb x c
      then S (findFirstRepeatedChar_count c rest)
      else findFirstRepeatedChar_count c rest
  end.

Fixpoint findFirstRepeatedChar_idxOf
    (c : lean_char) (chars : list lean_char) : nat :=
  match chars with
  | [] => 0%nat
  | x :: rest =>
      if lean_char_eqb x c
      then 0%nat
      else S (findFirstRepeatedChar_idxOf c rest)
  end.

Fixpoint findFirstRepeatedChar_zipIdxFrom
    (chars : list lean_char) (index : nat)
    : list (lean_char * nat) :=
  match chars with
  | [] => []
  | x :: rest =>
      (x, index) ::
      findFirstRepeatedChar_zipIdxFrom rest (S index)
  end.

Definition findFirstRepeatedChar_zipIdx
    (chars : list lean_char) : list (lean_char * nat) :=
  findFirstRepeatedChar_zipIdxFrom chars 0%nat.

Fixpoint findFirstRepeatedChar_findIdx
    (predicate : lean_char * nat -> bool)
    (entries : list (lean_char * nat)) : nat :=
  match entries with
  | [] => 0%nat
  | entry :: rest =>
      if predicate entry
      then 0%nat
      else S (findFirstRepeatedChar_findIdx predicate rest)
  end.

Definition findFirstRepeatedChar_secondIdx
    (chars : list lean_char) (c : lean_char) : nat :=
  let firstIdx := findFirstRepeatedChar_idxOf c chars in
  findFirstRepeatedChar_findIdx
    (fun entry =>
      let '(x, index) := entry in
      andb
        (lean_char_eqb x c)
        (negb (Nat.eqb index firstIdx)))
    (findFirstRepeatedChar_zipIdx chars).

Fixpoint findFirstRepeatedChar_pairwise_ne
    (chars : list lean_char) : Prop :=
  match chars with
  | [] => True
  | x :: rest =>
      Forall (fun y => lean_char_eqb x y = false) rest /\
      findFirstRepeatedChar_pairwise_ne rest
  end.

Definition findFirstRepeatedChar_postcond
    (s : lean_string)
    (result : option lean_char)
    (_h_precond : findFirstRepeatedChar_precond s) : Prop :=
  match result with
  | Some c =>
      (2 <= findFirstRepeatedChar_count c s)%nat /\
      findFirstRepeatedChar_pairwise_ne
        (firstn (findFirstRepeatedChar_secondIdx s c) s)
  | None =>
      findFirstRepeatedChar_pairwise_ne s
  end.

Theorem findFirstRepeatedChar_spec_satisfied
    (s : lean_string)
    (h_precond : findFirstRepeatedChar_precond s) :
  findFirstRepeatedChar_postcond
    s (findFirstRepeatedChar s h_precond) h_precond.
Admitted.
