(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_a2:
  the decimal digit block containing position 10^1987 in the concatenation
  of the positive integers has length 1984. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory numposrepTheory;

val putnam_1987_a2 =
  ``!seqind : num -> num.
    !seqsize : num -> num.
    !f : num -> num.
      seqind 1 = 1 /\
      (!i : num.
         2 <= i
         ==>
         seqind i =
           seqind (i - 1) + LENGTH (n2l 10 (i - 1))) /\
      (!i j : num.
         1 <= i /\ j < LENGTH (n2l 10 i)
         ==>
         seqsize (seqind i + j) = LENGTH (n2l 10 i)) /\
      (!n : num. f n = seqsize (10 EXP n))
      ==>
      f 1987 = 1984``;
