(*
  Statement-only formalization of VERINA corpus artifact verina_basic_83,
  catalog title "concat": the executable integer-array program fills a newly
  allocated array with the first input followed by the second and satisfies
  its unrestricted concatenation correctness contract. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val concat_getBang_def = Define `
  (concat_getBang
      ([] : int list) (index : num) = (0 : int)) /\
  (concat_getBang
      (value::rest) 0 = value) /\
  (concat_getBang
      (value::rest) (SUC index) =
     concat_getBang rest index)
`;

val concat_setBang_def = Define `
  (concat_setBang
      ([] : int list) (index : num) (value : int) =
     ([] : int list)) /\
  (concat_setBang
      (old::rest) 0 value =
     value::rest) /\
  (concat_setBang
      (old::rest) (SUC index) value =
     old::concat_setBang rest index value)
`;

val concat_precond_def = new_definition (
  "concat_precond_def",
  ``concat_precond (a : int list) (b : int list) <=> T``
);

val concat_loopFuel_def = Define `
  (concat_loopFuel
      0
      (a : int list)
      (b : int list)
      (n : num)
      (i : num)
      (c : int list) =
     c) /\
  (concat_loopFuel
      (SUC fuel)
      a
      b
      n
      i
      c =
     if i < n then
       let value =
         if i < LENGTH a then
           concat_getBang a i
         else
           concat_getBang b (i - LENGTH a)
       in
         concat_loopFuel
           fuel a b n (i + 1)
           (concat_setBang c i value)
     else
       c)
`;

val concat_loop_def = new_definition (
  "concat_loop_def",
  ``concat_loop
      (a : int list)
      (b : int list)
      (n : num)
      (i : num)
      (c : int list) =
      concat_loopFuel (SUC (n - i)) a b n i c``
);

val concat_def = new_definition (
  "concat_def",
  ``concat (a : int list) (b : int list) =
      let n = LENGTH a + LENGTH b in
        concat_loop
          a b n 0 (REPLICATE n (0 : int))``
);

val concat_postcond_def = new_definition (
  "concat_postcond_def",
  ``concat_postcond
      (a : int list)
      (b : int list)
      (result : int list) <=>
      LENGTH result = LENGTH a + LENGTH b /\
      (!k : num.
         k < LENGTH a ==>
         concat_getBang result k = concat_getBang a k) /\
      (!k : num.
         k < LENGTH b ==>
         concat_getBang result (k + LENGTH a) =
         concat_getBang b k)``
);

val concat_spec_satisfied =
  ``!(a : int list) (b : int list).
      concat_precond a b ==>
      concat_postcond a b (concat a b)``;
