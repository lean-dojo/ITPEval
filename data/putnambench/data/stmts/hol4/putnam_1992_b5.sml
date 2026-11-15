(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_b5:
  whether the factorial-normalized determinants of the specified growing
  diagonal matrices form a bounded sequence. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory rich_listTheory sortingTheory;
open pred_setTheory realTheory real_sigmaTheory;

val putnam_1992_b5 =
  ``!D : num -> real.
      (!n : num.
         D n =
         SIGMA
           (\p : num list.
              (-1 : real) pow
                CARD
                  {ij : num # num |
                     FST ij < SND ij /\
                     SND ij < n - 1 /\
                     EL (SND ij) p < EL (FST ij) p} *
              REAL_PROD_IMAGE
                (\i : num.
                   if i = EL i p then &(i + 3) else 1)
                (count (n - 1)))
           {p : num list | PERM p (GENLIST I (n - 1))})
      ==>
      let putnam_1992_b5_solution = F
      in
        ((?B : real.
            !n : num.
              2 <= n
              ==>
              abs (D n / &(FACT n)) <= B)
         <=>
         putnam_1992_b5_solution)``;
