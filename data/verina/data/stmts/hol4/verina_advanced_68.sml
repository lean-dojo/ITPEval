(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_68,
  catalog title "runLengthEncoder": the executable Unicode-string program
  replaces each consecutive run by its character followed by its decimal
  count, with the stated parsing, format, reconstruction, and emptiness
  correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory optionTheory pairTheory;

val runLengthEncoder_isUnicodeScalar_def = new_definition (
  "runLengthEncoder_isUnicodeScalar_def",
  ``runLengthEncoder_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val runLengthEncoder_isUnicodeString_def = new_definition (
  "runLengthEncoder_isUnicodeString_def",
  ``runLengthEncoder_isUnicodeString (s : num list) <=>
      EVERY runLengthEncoder_isUnicodeScalar s``
);

val runLengthEncoder_isDigit_def = new_definition (
  "runLengthEncoder_isDigit_def",
  ``runLengthEncoder_isDigit (c : num) <=>
      48 <= c /\ c <= 57``
);

val runLengthEncoder_chars_def = new_definition (
  "runLengthEncoder_chars_def",
  ``runLengthEncoder_chars (s : num list) = s``
);

val runLengthEncoder_charEq_def = new_definition (
  "runLengthEncoder_charEq_def",
  ``runLengthEncoder_charEq (c1 : num) (c2 : num) <=> c1 = c2``
);

val runLengthEncoder_precond_def = new_definition (
  "runLengthEncoder_precond_def",
  ``runLengthEncoder_precond (input : num list) <=>
      EVERY (\c : num. ~runLengthEncoder_isDigit c) input``
);

val runLengthEncoder_digitsFuel_def = Define `
  (runLengthEncoder_digitsFuel
      0
      (n : num) =
     ([] : num list)) /\
  (runLengthEncoder_digitsFuel
      (SUC fuel)
      n =
     if n < 10 then
       [n + 48]
     else
       runLengthEncoder_digitsFuel fuel (n DIV 10) ++
         [n MOD 10 + 48])
`;

val runLengthEncoder_numToString_def = new_definition (
  "runLengthEncoder_numToString_def",
  ``runLengthEncoder_numToString (n : num) =
      runLengthEncoder_digitsFuel (SUC n) n``
);

val runLengthEncoder_encode_def = Define `
  (runLengthEncoder_encode
      ([] : num list)
      (currentChar : num option)
      (count : num) =
     case currentChar of
       NONE => ([] : num list)
     | SOME c => [c] ++ runLengthEncoder_numToString count) /\
  (runLengthEncoder_encode
      (c::rest)
      currentChar
      count =
     case currentChar of
       NONE =>
         runLengthEncoder_encode rest (SOME c) 1
     | SOME c' =>
         if runLengthEncoder_charEq c c' then
           runLengthEncoder_encode rest (SOME c') (count + 1)
         else
           [c'] ++ runLengthEncoder_numToString count ++
             runLengthEncoder_encode rest (SOME c) 1)
`;

val runLengthEncoder_def = new_definition (
  "runLengthEncoder_def",
  ``runLengthEncoder (input : num list) =
      if input = [] then
        []
      else
        let firstChar =
          case runLengthEncoder_chars input of
            [] => NONE
          | c::cs => SOME c
        in
          runLengthEncoder_encode
            (TL (runLengthEncoder_chars input))
            firstChar
            1``
);

val runLengthEncoder_parseState_def = Define `
  (runLengthEncoder_parseState
      ([] : num list)
      (currentChar : num option)
      (currentCount : num option)
      (acc : (num # num) list) =
     case currentChar of
       NONE => acc
     | SOME c =>
         (case currentCount of
            NONE => acc
          | SOME n => (c, n)::acc)) /\
  (runLengthEncoder_parseState
      (c::cs)
      currentChar
      currentCount
      acc =
     if runLengthEncoder_isDigit c then
       case currentChar of
         NONE => ([] : (num # num) list)
       | SOME ch =>
           let digit = c - 48 in
           let newCount =
             case currentCount of
               NONE => digit
             | SOME n => n * 10 + digit
           in
             runLengthEncoder_parseState
               cs currentChar (SOME newCount) acc
     else
       let newAcc =
         case currentChar of
           NONE => acc
         | SOME ch =>
             (case currentCount of
                NONE => acc
              | SOME n => (ch, n)::acc)
       in
         runLengthEncoder_parseState cs (SOME c) NONE newAcc)
`;

val runLengthEncoder_parseEncodedString_def = new_definition (
  "runLengthEncoder_parseEncodedString_def",
  ``runLengthEncoder_parseEncodedString (s : num list) =
      REVERSE
        (runLengthEncoder_parseState
          (runLengthEncoder_chars s)
          NONE
          NONE
          ([] : (num # num) list))``
);

val runLengthEncoder_checkPairs_def = Define `
  (runLengthEncoder_checkPairs
      ([] : num list)
      (nowDigit : bool) =
     T) /\
  (runLengthEncoder_checkPairs
      (c::cs)
      nowDigit =
     if nowDigit /\ runLengthEncoder_isDigit c then
       runLengthEncoder_checkPairs cs T
     else
       case cs of
         [] => F
       | d::ds =>
           if runLengthEncoder_isDigit d then
             runLengthEncoder_checkPairs ds T
           else
             F)
`;

val runLengthEncoder_formatValid_def = new_definition (
  "runLengthEncoder_formatValid_def",
  ``runLengthEncoder_formatValid (result : num list) =
      runLengthEncoder_checkPairs
        (runLengthEncoder_chars result)
        F``
);

val runLengthEncoder_contentValid_def = new_definition (
  "runLengthEncoder_contentValid_def",
  ``runLengthEncoder_contentValid
      (input : num list)
      (result : num list) <=>
      FLAT
        (MAP
          (\pair : num # num.
             REPLICATE (SND pair) (FST pair))
          (runLengthEncoder_parseEncodedString result)) =
        runLengthEncoder_chars input``
);

val runLengthEncoder_nonEmptyValid_def = new_definition (
  "runLengthEncoder_nonEmptyValid_def",
  ``runLengthEncoder_nonEmptyValid
      (input : num list)
      (result : num list) <=>
      (input = [] <=> result = [])``
);

val runLengthEncoder_postcond_def = new_definition (
  "runLengthEncoder_postcond_def",
  ``runLengthEncoder_postcond
      (input : num list)
      (result : num list) <=>
      runLengthEncoder_formatValid result /\
      runLengthEncoder_contentValid input result /\
      runLengthEncoder_nonEmptyValid input result``
);

val runLengthEncoder_spec_satisfied =
  ``!input : num list.
      runLengthEncoder_isUnicodeString input ==>
      runLengthEncoder_precond input ==>
      runLengthEncoder_postcond
        input
        (runLengthEncoder input)``;
