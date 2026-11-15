(* Statement-only formalization of VERINA corpus artifact verina_advanced_68,
   catalog title "runLengthEncoder": executable run-length encoding of a
   digit-free Unicode string as characters followed by decimal run counts,
   together with parsing, format, reconstruction, and emptiness correctness
   conditions. This file contains no proof. *)

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

Definition runLengthEncoder_isDigit (c : lean_char) : bool :=
  match c with
  | LeanAscii a =>
      andb
        (Nat.leb 48 (Ascii.nat_of_ascii a))
        (Nat.leb (Ascii.nat_of_ascii a) 57)
  | LeanNonAscii _ _ _ => false
  end.

Definition runLengthEncoder_charToNat (c : lean_char) : nat :=
  match c with
  | LeanAscii a => Ascii.nat_of_ascii a
  | LeanNonAscii code _ _ => N.to_nat code
  end.

Definition runLengthEncoder_precond (input : lean_string) : Prop :=
  forallb (fun c => negb (runLengthEncoder_isDigit c)) input = true.

Fixpoint runLengthEncoder_digits_fuel
    (fuel n : nat) : lean_string :=
  match fuel with
  | O => []
  | S fuel' =>
      if Nat.ltb n 10
      then
        [LeanAscii (Ascii.ascii_of_nat (n + 48))]
      else
        runLengthEncoder_digits_fuel fuel' (Nat.div n 10) ++
        [LeanAscii
          (Ascii.ascii_of_nat (Nat.modulo n 10 + 48))]
  end.

Definition runLengthEncoder_numToString
    (n : nat) : lean_string :=
  runLengthEncoder_digits_fuel (S n) n.

Fixpoint runLengthEncoder_encode
    (input : lean_string)
    (currentChar : option lean_char)
    (count : nat) : lean_string :=
  match input with
  | [] =>
      match currentChar with
      | None => []
      | Some c =>
          [c] ++ runLengthEncoder_numToString count
      end
  | c :: rest =>
      match currentChar with
      | None =>
          runLengthEncoder_encode rest (Some c) 1
      | Some current =>
          if lean_char_eqb c current
          then
            runLengthEncoder_encode
              rest (Some current) (S count)
          else
            [current] ++ runLengthEncoder_numToString count ++
            runLengthEncoder_encode rest (Some c) 1
      end
  end.

Definition runLengthEncoder
    (input : lean_string)
    (_h_precond : runLengthEncoder_precond input) : lean_string :=
  match input with
  | [] => []
  | first :: rest =>
      runLengthEncoder_encode rest (Some first) 1
  end.

Fixpoint runLengthEncoder_parseState
    (remaining : lean_string)
    (currentChar : option lean_char)
    (currentCount : option nat)
    (acc : list (lean_char * nat))
    : list (lean_char * nat) :=
  match remaining with
  | [] =>
      match currentChar, currentCount with
      | Some c, Some n => (c, n) :: acc
      | _, _ => acc
      end
  | c :: cs =>
      if runLengthEncoder_isDigit c
      then
        match currentChar with
        | None => []
        | Some _ =>
            let digit :=
              runLengthEncoder_charToNat c - 48 in
            let newCount :=
              match currentCount with
              | None => digit
              | Some n => n * 10 + digit
              end in
            runLengthEncoder_parseState
              cs currentChar (Some newCount) acc
        end
      else
        let newAcc :=
          match currentChar, currentCount with
          | Some current, Some n =>
              (current, n) :: acc
          | _, _ => acc
          end in
        runLengthEncoder_parseState
          cs (Some c) None newAcc
  end.

Definition runLengthEncoder_parseEncodedString
    (encoded : lean_string) : list (lean_char * nat) :=
  rev
    (runLengthEncoder_parseState
      encoded None None []).

Fixpoint runLengthEncoder_checkPairs
    (chars : lean_string) (nowDigit : bool) : bool :=
  match chars with
  | [] => true
  | c :: cs =>
      if andb nowDigit (runLengthEncoder_isDigit c)
      then runLengthEncoder_checkPairs cs true
      else
        match cs with
        | [] => false
        | d :: ds =>
            if runLengthEncoder_isDigit d
            then runLengthEncoder_checkPairs ds true
            else false
        end
  end.

Fixpoint lean_char_list_eqb
    (xs ys : lean_string) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      andb (lean_char_eqb x y)
        (lean_char_list_eqb xs' ys')
  | _, _ => false
  end.

Definition runLengthEncoder_formatValid
    (result : lean_string) : bool :=
  runLengthEncoder_checkPairs result false.

Definition runLengthEncoder_contentValid
    (input result : lean_string) : bool :=
  let pairs :=
    runLengthEncoder_parseEncodedString result in
  let expanded :=
    flat_map
      (fun pair => repeat (fst pair) (snd pair))
      pairs in
  lean_char_list_eqb expanded input.

Definition runLengthEncoder_isEmpty
    (s : lean_string) : bool :=
  match s with
  | [] => true
  | _ :: _ => false
  end.

Definition runLengthEncoder_nonEmptyValid
    (input result : lean_string) : bool :=
  Bool.eqb
    (runLengthEncoder_isEmpty input)
    (runLengthEncoder_isEmpty result).

Definition runLengthEncoder_postcond
    (input result : lean_string)
    (_h_precond : runLengthEncoder_precond input) : Prop :=
  andb
    (runLengthEncoder_formatValid result)
    (andb
      (runLengthEncoder_contentValid input result)
      (runLengthEncoder_nonEmptyValid input result)) = true.

Theorem runLengthEncoder_spec_satisfied
    (input : lean_string)
    (h_precond : runLengthEncoder_precond input) :
  runLengthEncoder_postcond
    input (runLengthEncoder input h_precond) h_precond.
Admitted.
