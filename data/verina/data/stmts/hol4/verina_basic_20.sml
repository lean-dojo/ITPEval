(*
  Statement-only formalization of VERINA corpus artifact verina_basic_20,
  catalog title "uniqueProduct": the executable integer-list program
  multiplies each distinct input value at its first occurrence and satisfies
  the erase-duplicates product contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val uniqueProduct_precond_def = new_definition (
  "uniqueProduct_precond_def",
  ``uniqueProduct_precond (arr : int list) <=> T``
);

val uniqueProduct_loop_def = Define `
  (uniqueProduct_loop
      ([] : int list)
      (seen : int list)
      (product : int) =
     product) /\
  (uniqueProduct_loop
      (x::xs)
      seen
      product =
     if MEM x seen then
       uniqueProduct_loop xs seen product
     else
       uniqueProduct_loop xs (x::seen) (product * x))
`;

val uniqueProduct_def = new_definition (
  "uniqueProduct_def",
  ``uniqueProduct (arr : int list) =
      uniqueProduct_loop arr [] 1``
);

val uniqueProduct_eraseDupsLoop_def = Define `
  (uniqueProduct_eraseDupsLoop
      ([] : int list)
      (seen : int list) =
     REVERSE seen) /\
  (uniqueProduct_eraseDupsLoop
      (x::xs)
      seen =
     if MEM x seen then
       uniqueProduct_eraseDupsLoop xs seen
     else
       uniqueProduct_eraseDupsLoop xs (x::seen))
`;

val uniqueProduct_eraseDups_def = new_definition (
  "uniqueProduct_eraseDups_def",
  ``uniqueProduct_eraseDups (arr : int list) =
      uniqueProduct_eraseDupsLoop arr []``
);

val uniqueProduct_postcond_def = new_definition (
  "uniqueProduct_postcond_def",
  ``uniqueProduct_postcond
      (arr : int list) (result : int) <=>
      let expected =
        FOLDL
          (\acc x. acc * x)
          (1 : int)
          (uniqueProduct_eraseDups arr)
      in
        result - expected = 0 /\
        expected - result = 0``
);

val uniqueProduct_spec_satisfied =
  ``!arr : int list.
      uniqueProduct_precond arr ==>
      uniqueProduct_postcond arr (uniqueProduct arr)``;
