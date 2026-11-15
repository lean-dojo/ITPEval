(*
  Statement-only formalization of VERINA corpus artifact verina_basic_86,
  catalog title "rotate": the executable integer-array loop constructs a left
  rotation by a nonnegative integer offset using Lean-style Euclidean modular
  indexing and states its size and pointwise correctness contract. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val rotate_intEmod_def = new_definition (
  "rotate_intEmod_def",
  ``rotate_intEmod (x : int) (y : int) =
      if y = 0 then
        x
      else if y < 0 then
        x % ~y
      else
        x % y``
);

val rotate_intToNat_def = new_definition (
  "rotate_intToNat_def",
  ``rotate_intToNat (x : int) =
      if x < 0 then 0 else Num x``
);

val rotate_getBang_def = new_definition (
  "rotate_getBang_def",
  ``rotate_getBang (arr : int list) (i : num) =
      if i < LENGTH arr then EL i arr else (0 : int)``
);

val rotate_setBang_def = new_definition (
  "rotate_setBang_def",
  ``rotate_setBang
      (arr : int list) (i : num) (value : int) =
      if i < LENGTH arr then LUPDATE value i arr else arr``
);

val rotate_precond_def = new_definition (
  "rotate_precond_def",
  ``rotate_precond (a : int list) (offset : int) <=>
      0 <= offset``
);

val rotateAuxFuel_def = Define `
  (rotateAuxFuel
      0
      (a : int list)
      (offset : int)
      (i : num)
      (len : num)
      (b : int list) =
     b) /\
  (rotateAuxFuel
      (SUC fuel)
      a
      offset
      i
      len
      b =
     if i < len then
       let idx_int =
         rotate_intEmod
           (int_of_num i + offset)
           (int_of_num len)
       in
       let idx_int_adjusted =
         if idx_int < 0 then
           idx_int + int_of_num len
         else
           idx_int
       in
       let idx_nat = rotate_intToNat idx_int_adjusted in
       let new_b =
         rotate_setBang b i (rotate_getBang a idx_nat)
       in
         rotateAuxFuel
           fuel a offset (i + 1) len new_b
     else
       b)
`;

val rotateAux_def = new_definition (
  "rotateAux_def",
  ``rotateAux
      (a : int list)
      (offset : int)
      (i : num)
      (len : num)
      (b : int list) =
      rotateAuxFuel
        (SUC (len - i)) a offset i len b``
);

val rotate_def = new_definition (
  "rotate_def",
  ``rotate (a : int list) (offset : int) =
      let len = LENGTH a in
      let default_val =
        if len > 0 then rotate_getBang a 0 else (0 : int)
      in
      let b0 = REPLICATE len default_val in
        rotateAux a offset 0 len b0``
);

val rotate_postcond_def = new_definition (
  "rotate_postcond_def",
  ``rotate_postcond
      (a : int list)
      (offset : int)
      (result : int list) <=>
      LENGTH result = LENGTH a /\
      (!i : num.
         i < LENGTH a ==>
         rotate_getBang result i =
         rotate_getBang
           a
           (rotate_intToNat
             (rotate_intEmod
               (int_of_num i + offset)
               (int_of_num (LENGTH a)))))``
);

val rotate_spec_satisfied =
  ``!(a : int list) (offset : int).
      rotate_precond a offset ==>
      rotate_postcond a offset (rotate a offset)``;
