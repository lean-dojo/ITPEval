(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_67,
  catalog title "runLengthEncode": the executable program groups consecutive
  equal characters into positive-length runs whose decoding is the original
  Unicode string. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pairTheory;

val runLengthEncode_isUnicodeScalar_def = new_definition (
  "runLengthEncode_isUnicodeScalar_def",
  ``runLengthEncode_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val runLengthEncode_isUnicodeString_def = new_definition (
  "runLengthEncode_isUnicodeString_def",
  ``runLengthEncode_isUnicodeString (s : num list) <=>
      EVERY runLengthEncode_isUnicodeScalar s``
);

val runLengthEncode_precond_def = new_definition (
  "runLengthEncode_precond_def",
  ``runLengthEncode_precond (s : num list) <=> T``
);

val runLengthEncode_encodeAux_def = Define `
  (runLengthEncode_encodeAux
      (acc : (num # num) list) ([] : num list) =
     REVERSE acc) /\
  (runLengthEncode_encodeAux
      ([] : (num # num) list) (h::t) =
     runLengthEncode_encodeAux [(h, 1)] t) /\
  (runLengthEncode_encodeAux
      ((ch, count)::accTail) (h::t) =
     if ch = h then
       runLengthEncode_encodeAux
         ((ch, count + 1)::accTail) t
     else
       runLengthEncode_encodeAux
         ((h, 1)::(ch, count)::accTail) t)
`;

val runLengthEncode_def = new_definition (
  "runLengthEncode_def",
  ``runLengthEncode (s : num list) =
      let chars = s in
      let encoded =
        runLengthEncode_encodeAux
          ([] : (num # num) list) chars
      in
        encoded``
);

val decodeRLE_def = Define `
  (decodeRLE
      ([] : (num # num) list) =
     ([] : num list)) /\
  (decodeRLE
      ((ch, count)::tail) =
     REPLICATE count ch ++ decodeRLE tail)
`;

val runLengthEncode_postcond_def = new_definition (
  "runLengthEncode_postcond_def",
  ``runLengthEncode_postcond
      (s : num list)
      (result : (num # num) list) <=>
      EVERY (\pair : num # num. 0 < SND pair) result /\
      (!i : num.
         i < LENGTH result - 1 ==>
         ~(FST (EL i result) =
           FST (EL (i + 1) result))) /\
      decodeRLE result = s``
);

val runLengthEncode_spec_satisfied =
  ``!s : num list.
      runLengthEncode_isUnicodeString s ==>
      runLengthEncode_precond s ==>
      runLengthEncode_postcond
        s (runLengthEncode s)``;
