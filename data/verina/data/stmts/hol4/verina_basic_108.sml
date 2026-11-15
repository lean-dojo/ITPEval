(*
  Statement-only formalization of VERINA corpus artifact verina_basic_108,
  catalog title "below_zero": the executable program builds integer prefix
  sums from zero and reports whether any resulting prefix sum is negative,
  under its stated correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory;

val below_zero_precond_def = new_definition (
  "below_zero_precond_def",
  ``below_zero_precond (operations : int list) <=> T``
);

val below_zero_lastDefault_def = new_definition (
  "below_zero_lastDefault_def",
  ``below_zero_lastDefault (xs : int list) =
      if xs = [] then (0 : int) else LAST xs``
);

val buildS_def = new_definition (
  "buildS_def",
  ``buildS (operations : int list) =
      FOLDL
        (\acc op.
           acc ++ [below_zero_lastDefault acc + op])
        [0]
        operations``
);

val below_zero_check_negative_def = Define `
  (below_zero_check_negative ([] : int list) = F) /\
  (below_zero_check_negative (x::xs) =
     if x < 0 then T else below_zero_check_negative xs)
`;

val below_zero_def = new_definition (
  "below_zero_def",
  ``below_zero (operations : int list) =
      let s = buildS operations in
      let result = below_zero_check_negative s in
        (s, result)``
);

val below_zero_getOpt_def = new_definition (
  "below_zero_getOpt_def",
  ``below_zero_getOpt (xs : int list) (i : num) =
      if i < LENGTH xs then SOME (EL i xs) else NONE``
);

val below_zero_getBang_def = new_definition (
  "below_zero_getBang_def",
  ``below_zero_getBang (xs : int list) (i : num) =
      if i < LENGTH xs then EL i xs else (0 : int)``
);

val below_zero_postcond_def = new_definition (
  "below_zero_postcond_def",
  ``below_zero_postcond
      (operations : int list)
      (output : int list # bool) <=>
      let s = FST output in
      let result = SND output in
        LENGTH s = LENGTH operations + 1 /\
        below_zero_getOpt s 0 = SOME 0 /\
        EVERY
          (\i : num.
             below_zero_getOpt s (i + 1) =
             SOME
               (below_zero_getBang s i +
                below_zero_getBang operations i))
          (COUNT_LIST (LENGTH s - 1)) /\
        ((result = T) ==>
          EXISTS
            (\i : num. below_zero_getBang s (i + 1) < 0)
            (COUNT_LIST (LENGTH operations))) /\
        ((result = F) ==>
          EVERY (\x : int. 0 <= x) s)``
);

val below_zero_spec_satisfied =
  ``!operations : int list.
      below_zero_precond operations ==>
      below_zero_postcond operations (below_zero operations)``;
