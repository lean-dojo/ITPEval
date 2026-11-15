(*
  Statement-only formalization of Hundred Theorems artifact 077, "Sum of kth Powers".
  Faulhaber's formula expresses each finite sum of natural-number powers using the
  recursively specified Bernoulli numbers and their Bernoulli polynomials. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory pred_setTheory realTheory real_sigmaTheory;

val sum_of_kth_powers =
  ``!bernoulli : num -> real.
      !bernpoly : num -> real -> real.
        bernoulli 0 = 1 /\
        (!r : num.
           bernoulli (SUC r) =
           -SIGMA
              (\j : num. &(binomial (r + 2) j) * bernoulli j)
              (count (SUC r)) /
           (&r + 2)) /\
        (!r : num. !x : real.
           bernpoly r x =
           SIGMA
             (\k : num.
                &(binomial r k) * bernoulli k * x pow (r - k))
             (count (SUC r)))
        ==>
        !m n : num.
          SIGMA (\k : num. &k pow m) (count (SUC n)) =
          (bernpoly (SUC m) (&n + 1) - bernpoly (SUC m) 0) /
          (&m + 1)``;
