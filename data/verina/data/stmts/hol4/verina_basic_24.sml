(*
  Statement-only formalization of VERINA corpus artifact verina_basic_24,
  catalog title "firstEvenOddDifference": the executable left-to-right scan
  returns the first even integer minus the first odd integer under the stated
  existence precondition and satisfies the index-minimality postcondition.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory;

val isEven_def = new_definition (
  "isEven_def",
  ``isEven (n : int) <=> n % 2 = 0``
);

val isOdd_def = new_definition (
  "isOdd_def",
  ``isOdd (n : int) <=> n % 2 <> 0``
);

val firstEvenOddDifference_precond_def = new_definition (
  "firstEvenOddDifference_precond_def",
  ``firstEvenOddDifference_precond (a : int list) <=>
      LENGTH a > 1 /\
      EXISTS (\x : int. isEven x) a /\
      EXISTS (\x : int. isOdd x) a``
);

val firstEvenOddDifference_nthD_def = Define `
  (firstEvenOddDifference_nthD
      (index : num) ([] : int list) = (0 : int)) /\
  (firstEvenOddDifference_nthD
      0 (x::xs) = x) /\
  (firstEvenOddDifference_nthD
      (SUC index) (x::xs) =
     firstEvenOddDifference_nthD index xs)
`;

val firstEvenOddDifference_findFirstEvenOddFuel_def = Define `
  (firstEvenOddDifference_findFirstEvenOddFuel
      (a : int list)
      (i : num)
      (firstEven : num option)
      (firstOdd : num option)
      0 =
     (0 : int)) /\
  (firstEvenOddDifference_findFirstEvenOddFuel
      a i firstEven firstOdd (SUC fuel) =
     if i < LENGTH a then
       let x = firstEvenOddDifference_nthD i a in
       let nextEven =
         if firstEven = NONE /\ isEven x then SOME i else firstEven in
       let nextOdd =
         if firstOdd = NONE /\ isOdd x then SOME i else firstOdd in
         case nextEven of
           NONE =>
             firstEvenOddDifference_findFirstEvenOddFuel
               a (i + 1) nextEven nextOdd fuel
         | SOME evenIndex =>
             case nextOdd of
               NONE =>
                 firstEvenOddDifference_findFirstEvenOddFuel
                   a (i + 1) nextEven nextOdd fuel
             | SOME oddIndex =>
                 firstEvenOddDifference_nthD evenIndex a -
                 firstEvenOddDifference_nthD oddIndex a
     else
       0)
`;

val firstEvenOddDifference_findFirstEvenOdd_def = new_definition (
  "firstEvenOddDifference_findFirstEvenOdd_def",
  ``firstEvenOddDifference_findFirstEvenOdd
      (a : int list)
      (i : num)
      (firstEven : num option)
      (firstOdd : num option) =
      firstEvenOddDifference_findFirstEvenOddFuel
        a i firstEven firstOdd (LENGTH a - i + 1)``
);

val firstEvenOddDifference_def = new_definition (
  "firstEvenOddDifference_def",
  ``firstEvenOddDifference (a : int list) =
      firstEvenOddDifference_findFirstEvenOdd a 0 NONE NONE``
);

val firstEvenOddDifference_postcond_def = new_definition (
  "firstEvenOddDifference_postcond_def",
  ``firstEvenOddDifference_postcond
      (a : int list) (result : int) <=>
      ?i j : num.
        i < LENGTH a /\
        j < LENGTH a /\
        isEven (firstEvenOddDifference_nthD i a) /\
        isOdd (firstEvenOddDifference_nthD j a) /\
        result =
          firstEvenOddDifference_nthD i a -
          firstEvenOddDifference_nthD j a /\
        (!k : num.
          k < i ==>
          isOdd (firstEvenOddDifference_nthD k a)) /\
        (!k : num.
          k < j ==>
          isEven (firstEvenOddDifference_nthD k a))``
);

val firstEvenOddDifference_spec_satisfied =
  ``!a : int list.
      firstEvenOddDifference_precond a ==>
      firstEvenOddDifference_postcond
        a (firstEvenOddDifference a)``;
