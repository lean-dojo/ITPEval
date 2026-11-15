(*
  Statement-only formalization of VERINA corpus artifact verina_basic_30,
  catalog title "elementWiseModulo": the executable array program computes
  Lean-style Euclidean remainders elementwise for equal nonempty integer
  arrays with nonzero divisors, with its length and pointwise correctness
  contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val elementWiseModulo_intEmod_def = new_definition (
  "elementWiseModulo_intEmod_def",
  ``elementWiseModulo_intEmod (x : int) (y : int) =
      if y = 0 then
        x
      else if y < 0 then
        x % ~y
      else
        x % y``
);

val elementWiseModulo_getD_def = new_definition (
  "elementWiseModulo_getD_def",
  ``elementWiseModulo_getD (xs : int list) (i : num) =
      if i < LENGTH xs then EL i xs else 0``
);

val elementWiseModulo_precond_def = new_definition (
  "elementWiseModulo_precond_def",
  ``elementWiseModulo_precond
      (a : int list) (b : int list) <=>
      LENGTH a = LENGTH b /\
      0 < LENGTH a /\
      (!i : num.
         i < LENGTH b ==>
         elementWiseModulo_getD b i <> 0)``
);

val elementWiseModulo_def = new_definition (
  "elementWiseModulo_def",
  ``elementWiseModulo (a : int list) (b : int list) =
      GENLIST
        (\i : num.
           elementWiseModulo_intEmod
             (elementWiseModulo_getD a i)
             (elementWiseModulo_getD b i))
        (LENGTH a)``
);

val elementWiseModulo_postcond_def = new_definition (
  "elementWiseModulo_postcond_def",
  ``elementWiseModulo_postcond
      (a : int list) (b : int list) (result : int list) <=>
      LENGTH result = LENGTH a /\
      (!i : num.
         i < LENGTH result ==>
         elementWiseModulo_getD result i =
         elementWiseModulo_intEmod
           (elementWiseModulo_getD a i)
           (elementWiseModulo_getD b i))``
);

val elementWiseModulo_spec_satisfied =
  ``!(a : int list) (b : int list).
      elementWiseModulo_precond a b ==>
      elementWiseModulo_postcond
        a b (elementWiseModulo a b)``;
