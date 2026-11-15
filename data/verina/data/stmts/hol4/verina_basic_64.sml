(*
  Statement-only formalization of VERINA corpus artifact verina_basic_64,
  catalog title "insert": the executable Unicode-character array program
  inserts the first p characters of one array at a natural position within
  the first l characters of another array and satisfies its size and
  pointwise correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val insert_isUnicodeScalar_def = new_definition (
  "insert_isUnicodeScalar_def",
  ``insert_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val insert_isUnicodeString_def = new_definition (
  "insert_isUnicodeString_def",
  ``insert_isUnicodeString (s : num list) <=>
      EVERY insert_isUnicodeScalar s``
);

val insert_nthD_def = new_definition (
  "insert_nthD_def",
  ``insert_nthD (xs : num list) (index : num) =
      if index < LENGTH xs then EL index xs else 0``
);

val insert_precond_def = new_definition (
  "insert_precond_def",
  ``insert_precond
      (oline : num list) (l : num)
      (nl : num list) (p : num) (atPos : num) <=>
      l <= LENGTH oline /\
      p <= LENGTH nl /\
      atPos <= l``
);

val insert_def = new_definition (
  "insert_def",
  ``insert
      (oline : num list) (l : num)
      (nl : num list) (p : num) (atPos : num) =
      let result = REPLICATE (l + p) 32 in
      let result =
        FOLDL
          (\acc : num list. \i : num.
             if i < atPos then
               LUPDATE (insert_nthD oline i) i acc
             else
               acc)
          result
          (GENLIST (\i : num. i) l)
      in
      let result =
        FOLDL
          (\acc : num list. \i : num.
             LUPDATE
               (insert_nthD nl i)
               (atPos + i)
               acc)
          result
          (GENLIST (\i : num. i) p)
      in
      let result =
        FOLDL
          (\acc : num list. \i : num.
             if atPos <= i then
               LUPDATE
                 (insert_nthD oline i)
                 (i + p)
                 acc
             else
               acc)
          result
          (GENLIST (\i : num. i) l)
      in
        result``
);

val insert_postcond_def = new_definition (
  "insert_postcond_def",
  ``insert_postcond
      (oline : num list) (l : num)
      (nl : num list) (p : num) (atPos : num)
      (result : num list) <=>
      insert_isUnicodeString result /\
      LENGTH result = l + p /\
      (!i : num.
         i < p ==>
         insert_nthD result (atPos + i) =
         insert_nthD nl i) /\
      (!i : num.
         i < atPos ==>
         insert_nthD result i =
         insert_nthD oline i) /\
      (!i : num.
         i < l - atPos ==>
         insert_nthD result (atPos + p + i) =
         insert_nthD oline (atPos + i))``
);

val insert_spec_satisfied =
  ``!(oline : num list) (l : num)
      (nl : num list) (p : num) (atPos : num).
      insert_isUnicodeString oline ==>
      insert_isUnicodeString nl ==>
      insert_precond oline l nl p atPos ==>
      insert_postcond
        oline l nl p atPos
        (insert oline l nl p atPos)``;
