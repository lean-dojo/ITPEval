(*
  Statement-only formalization of PutnamBench artifact putnam_1969_a1:
  the possible ranges of real bivariate polynomials are exactly singletons,
  one-sided intervals, and the whole real line. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory listTheory realTheory polyTheory;

val putnam_1969_a1 =
  ``{s : real set |
       ?f : real list list.
         s =
           {z : real |
              ?x y : real.
                poly (MAP (\p : real list. poly p y) f) x = z}} =
    {s : real set |
       (?a : real. s = {a}) \/
       (?a : real. s = {x : real | a <= x}) \/
       (?a : real. s = {x : real | x <= a}) \/
       (?a : real. s = {x : real | x < a}) \/
       (?a : real. s = {x : real | a < x}) \/
       s = UNIV}``;
