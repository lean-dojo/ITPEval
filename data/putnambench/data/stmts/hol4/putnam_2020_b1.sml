(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_b1:
  the alternating sum of the cubes from 1 through 2020, weighted by binary
  digit-sum parity, has remainder 1990 modulo 2020. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory;

val putnam_2020_b1 =
  ``!d : num -> num. !S : int.
      (!n : num.
         d n =
         if n = 0 then 0
         else n MOD 2 + d (n DIV 2)) /\
      S =
        FOLDR
          (\k acc.
             (~1 : int) ** (d k) * int_of_num (k EXP 3) + acc)
          (0 : int)
          (GENLIST SUC 2020)
      ==>
      S % 2020 = 1990``;
