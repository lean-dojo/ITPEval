(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_b2:
  for positive natural numbers m and n, the factorial ratio at m + n is
  strictly less than the product of the corresponding ratios at m and n.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory ratTheory;

val putnam_2004_b2 =
  ``!m n : num.
      0 < m /\ 0 < n
      ==>
      rat_of_num (FACT (m + n)) /
        rat_expn (rat_of_num (m + n)) (m + n) <
      (rat_of_num (FACT m) / rat_expn (rat_of_num m) m) *
        (rat_of_num (FACT n) / rat_expn (rat_of_num n) n)``;
