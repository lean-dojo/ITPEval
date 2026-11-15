(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_a1:
  exactly one prime has an ordinary base-10 expansion whose digits alternate
  between 1 and 0, beginning and ending with 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory numposrepTheory pred_setTheory primeTheory;

val putnam_1989_a1 =
  ``{p : num |
       0 < p /\
       prime p /\
       ODD (LENGTH (n2l 10 p)) /\
       (!i : num.
          i < LENGTH (n2l 10 p)
          ==>
          EL i (n2l 10 p) = if EVEN i then 1 else 0)}
      HAS_SIZE 1``;
