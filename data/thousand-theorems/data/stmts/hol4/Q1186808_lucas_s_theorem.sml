(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1186808, "Lucas's theorem": for a prime p, a binomial coefficient is
  congruent modulo p to the product of the binomial coefficients of the
  corresponding base-p digits. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory listTheory;

val lucas_theorem =
  ``!n k p a : num.
      prime p /\
      n < p EXP a /\
      k < p EXP a
      ==>
      binomial n k MOD p =
      PROD
        (GENLIST
           (\i : num.
              binomial
                ((n DIV (p EXP i)) MOD p)
                ((k DIV (p EXP i)) MOD p))
           a) MOD p``;
