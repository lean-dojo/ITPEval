(* Statement-only formalization of VERINA corpus artifact verina_advanced_66,
   catalog title "reverseWords": executable reversal of the words in a
   Unicode string after removing empty space-delimited pieces, with single
   spaces in the result, together with its correctness contract. This file
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

Definition reverseWords_space : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 32).

Definition reverseWords_isSpace (c : lean_char) : bool :=
  match c with
  | LeanAscii a => Nat.eqb (Ascii.nat_of_ascii a) 32
  | LeanNonAscii _ _ _ => false
  end.

Fixpoint reverseWords_splitOnSpace_aux
    (remaining current : lean_string) : list lean_string :=
  match remaining with
  | [] => [rev current]
  | c :: rest =>
      if reverseWords_isSpace c
      then
        rev current ::
          reverseWords_splitOnSpace_aux rest []
      else
        reverseWords_splitOnSpace_aux rest (c :: current)
  end.

Definition reverseWords_splitOnSpace
    (words_str : lean_string) : list lean_string :=
  reverseWords_splitOnSpace_aux words_str [].

Fixpoint reverseWords_filterNonEmpty
    (words : list lean_string) : list lean_string :=
  match words with
  | [] => []
  | word :: rest =>
      match word with
      | [] => reverseWords_filterNonEmpty rest
      | _ :: _ => word :: reverseWords_filterNonEmpty rest
      end
  end.

Definition reverseWords_nonemptyb (word : lean_string) : bool :=
  match word with
  | [] => false
  | _ :: _ => true
  end.

Fixpoint reverseWords_joinWithSpace
    (words : list lean_string) : lean_string :=
  match words with
  | [] => []
  | word :: rest =>
      match rest with
      | [] => word
      | _ :: _ =>
          word ++ [reverseWords_space] ++
            reverseWords_joinWithSpace rest
      end
  end.

Fixpoint reverseWords_intercalate
    (separator : lean_string)
    (words : list lean_string) : lean_string :=
  match words with
  | [] => []
  | word :: rest =>
      match rest with
      | [] => word
      | _ :: _ =>
          word ++ separator ++
            reverseWords_intercalate separator rest
      end
  end.

Definition reverseWords_precond
    (_words_str : lean_string) : Prop :=
  True.

Definition reverseWords
    (words_str : lean_string)
    (_h_precond : reverseWords_precond words_str) : lean_string :=
  let rawWords := reverseWords_splitOnSpace words_str in
  let filteredWords := reverseWords_filterNonEmpty rawWords in
  let revWords := rev filteredWords in
  reverseWords_joinWithSpace revWords.

Definition reverseWords_postcond
    (words_str result : lean_string)
    (_h_precond : reverseWords_precond words_str) : Prop :=
  exists words : list lean_string,
    words =
      filter reverseWords_nonemptyb
        (reverseWords_splitOnSpace words_str) /\
    result =
      reverseWords_intercalate
        [reverseWords_space] (rev words).

Theorem reverseWords_spec_satisfied
    (words_str : lean_string)
    (h_precond : reverseWords_precond words_str) :
  reverseWords_postcond
    words_str (reverseWords words_str h_precond) h_precond.
Admitted.
