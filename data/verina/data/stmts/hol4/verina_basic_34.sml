(*
  Statement-only formalization of VERINA corpus artifact verina_basic_34,
  catalog title "findEvenNumbers": the executable left-fold program extracts
  exactly the even integers from an input array in their original order and
  satisfies its multiplicity, membership, and index-order contract. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val isEven_def = new_definition (
  "isEven_def",
  ``isEven (n : int) <=> n % 2 = 0``
);

val findEvenNumbers_precond_def = new_definition (
  "findEvenNumbers_precond_def",
  ``findEvenNumbers_precond (arr : int list) <=> T``
);

val findEvenNumbers_def = new_definition (
  "findEvenNumbers_def",
  ``findEvenNumbers (arr : int list) =
      FOLDL
        (\acc x.
          if isEven x then acc ++ [x] else acc)
        ([] : int list)
        arr``
);

val findEvenNumbers_count_def = new_definition (
  "findEvenNumbers_count_def",
  ``findEvenNumbers_count (x : int) (xs : int list) =
      LENGTH (FILTER (\y : int. y = x) xs)``
);

val findEvenNumbers_idxOf_def = Define `
  (findEvenNumbers_idxOf
      (value : int) ([] : int list) = 0) /\
  (findEvenNumbers_idxOf
      value (head::tail) =
     if head = value then
       0
     else
       SUC (findEvenNumbers_idxOf value tail))
`;

val findEvenNumbers_postcond_def = new_definition (
  "findEvenNumbers_postcond_def",
  ``findEvenNumbers_postcond
      (arr : int list) (result : int list) <=>
      EVERY
        (\x : int.
          isEven x /\
          MEM x arr /\
          findEvenNumbers_count x result =
            findEvenNumbers_count x arr)
        result /\
      EVERY
        (\x : int.
          isEven x ==> MEM x result)
        arr /\
      EVERY
        (\x : int.
          EVERY
            (\y : int.
              isEven x ==>
              isEven y ==>
              findEvenNumbers_idxOf x arr <=
                findEvenNumbers_idxOf y arr ==>
              findEvenNumbers_idxOf x result <=
                findEvenNumbers_idxOf y result)
            arr)
        arr``
);

val findEvenNumbers_spec_satisfied =
  ``!arr : int list.
      findEvenNumbers_precond arr ==>
      findEvenNumbers_postcond
        arr (findEvenNumbers arr)``;
