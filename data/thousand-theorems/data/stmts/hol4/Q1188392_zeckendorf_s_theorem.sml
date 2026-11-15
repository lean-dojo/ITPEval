(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1188392, "Zeckendorf's theorem": for the Fibonacci sequence determined by
  its initial values and recurrence, natural numbers are equivalent to lists
  of nonconsecutive indices at least two, with Fibonacci summation as the
  inverse. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory;

val zeckendorf_equiv =
  ``let is_fibonacci =
      \f : num -> num.
        f 0 = 0 /\
        f 1 = 1 /\
        (!n : num. f (n + 2) = f (n + 1) + f n)
    in
    let is_zeckendorf_rep =
      \l : num list.
        !i : num.
          i + 1 < LENGTH (l ++ [0])
          ==>
          EL (i + 1) (l ++ [0]) + 2 <= EL i (l ++ [0])
    in
      !f : num -> num.
        is_fibonacci f
        ==>
        ?encode : num -> num list.
          (!n : num. is_zeckendorf_rep (encode n)) /\
          (!n : num. SUM (MAP f (encode n)) = n) /\
          (!l : num list.
             is_zeckendorf_rep l
             ==>
             encode (SUM (MAP f l)) = l)``;
