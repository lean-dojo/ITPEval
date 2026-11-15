(* Statement-only formalization of VERINA corpus artifact verina_advanced_71,
   catalog title "shortestBeautifulSubstring": executable enumeration and
   selection of the shortest binary substring containing exactly k ones, with
   lexicographic tie-breaking and its optimality contract. This file contains
   no proof. *)

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

Definition lean_char_code (c : lean_char) : N :=
  match c with
  | LeanAscii a => N.of_nat (Ascii.nat_of_ascii a)
  | LeanNonAscii code _ _ => code
  end.

Definition lean_char_eqb (x y : lean_char) : bool :=
  N.eqb (lean_char_code x) (lean_char_code y).

Definition shortestBeautifulSubstring_zero : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 48).

Definition shortestBeautifulSubstring_one : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 49).

Fixpoint lean_string_eqb (xs ys : lean_string) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      andb (lean_char_eqb x y) (lean_string_eqb xs' ys')
  | _, _ => false
  end.

Fixpoint lean_string_ltb (xs ys : lean_string) : bool :=
  match xs, ys with
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs', y :: ys' =>
      if lean_char_eqb x y
      then lean_string_ltb xs' ys'
      else N.ltb (lean_char_code x) (lean_char_code y)
  end.

Fixpoint lean_string_leb (xs ys : lean_string) : bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs', y :: ys' =>
      if lean_char_eqb x y
      then lean_string_leb xs' ys'
      else N.ltb (lean_char_code x) (lean_char_code y)
  end.

Definition countOnes (lst : list lean_char) : nat :=
  fold_left
    (fun acc c =>
      if lean_char_eqb c shortestBeautifulSubstring_one
      then S acc
      else acc)
    lst 0.

Definition shortestBeautifulSubstring_precond
    (s : lean_string) (_k : nat) : Prop :=
  forallb
    (fun c =>
      orb
        (lean_char_eqb c shortestBeautifulSubstring_zero)
        (lean_char_eqb c shortestBeautifulSubstring_one))
    s = true.

Definition listToString (lst : list lean_char) : lean_string :=
  lst.

Definition isLexSmaller
    (a b : list lean_char) : bool :=
  lean_string_ltb (listToString a) (listToString b).

Definition allSubstrings
    (s : list lean_char) : list (list lean_char) :=
  let n := length s in
  flat_map
    (fun i =>
      map
        (fun j => firstn (S j) (skipn i s))
        (seq 0 (n - i)))
    (seq 0 n).

Definition shortestBeautifulSubstring_compare
    (a b : list lean_char) : bool :=
  orb
    (Nat.ltb (length a) (length b))
    (andb
      (Nat.eqb (length a) (length b))
      (isLexSmaller a b)).

Definition shortestBeautifulSubstring
    (s : lean_string)
    (k : nat)
    (_h_precond : shortestBeautifulSubstring_precond s k)
    : lean_string :=
  let chars := s in
  let candidates :=
    filter
      (fun sub => Nat.eqb (countOnes sub) k)
      (allSubstrings chars) in
  let best :=
    fold_left
      (fun acc cur =>
        match acc with
        | None => Some cur
        | Some currentBest =>
            if shortestBeautifulSubstring_compare cur currentBest
            then Some cur
            else Some currentBest
        end)
      candidates None in
  match best with
  | Some b => listToString b
  | None => []
  end.

Definition shortestBeautifulSubstring_postSubstrings
    (chars : list lean_char) : list (list lean_char) :=
  flat_map
    (fun i =>
      map
        (fun len => firstn len (skipn i chars))
        (seq 0 (length chars - i + 1)))
    (seq 0 (length chars)).

Definition shortestBeautifulSubstring_nonemptyb
    (s : lean_string) : bool :=
  match s with
  | [] => false
  | _ :: _ => true
  end.

Definition shortestBeautifulSubstring_postcond
    (s : lean_string)
    (k : nat)
    (result : lean_string)
    (_h_precond : shortestBeautifulSubstring_precond s k) : Prop :=
  let chars := s in
  let substrings :=
    shortestBeautifulSubstring_postSubstrings chars in
  let beautiful :=
    filter
      (fun sub => Nat.eqb (countOnes sub) k)
      substrings in
  let targets :=
    filter
      shortestBeautifulSubstring_nonemptyb
      (map listToString beautiful) in
  (result = [] /\ targets = []) \/
  (In result targets /\
   forall r,
     In r targets ->
     (length result < length r)%nat \/
     (length r = length result /\
      lean_string_leb result r = true)).

Theorem shortestBeautifulSubstring_spec_satisfied
    (s : lean_string)
    (k : nat)
    (h_precond : shortestBeautifulSubstring_precond s k) :
  shortestBeautifulSubstring_postcond
    s k (shortestBeautifulSubstring s k h_precond) h_precond.
Admitted.
