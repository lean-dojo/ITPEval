(*
  Statement-only formalization of "The Central Limit Theorem" from Hundred Theorems item 047.
  It states the zero-mean and centered i.i.d. finite-variance forms as weak convergence of
  normalized partial-sum distributions to the standard normal distribution. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory iterateTheory realTheory transcTheory;
open topologyTheory real_topologyTheory extrealTheory measureTheory borelTheory;
open lebesgueTheory lebesgue_measureTheory probabilityTheory;

val central_limit_theorem_zero_mean =
  ``!(p : 'a p_space) (X : num -> 'a -> real)
      (mu : real measure) (sigma : real) (S : num -> 'a -> real).
      let std_normal_density =
        \x : real. (1 / sqrt (2 * pi)) * exp (-(x pow 2) / 2)
      in
      let std_normal_measure =
        density_measure lborel (Normal o std_normal_density)
      in
        prob_space p /\
        measure_space (space borel, subsets borel, mu) /\
        (!n. random_variable (X n) p borel) /\
        indep_vars p X (\i. borel) UNIV /\
        (!n. expectation p (Normal o X n) = 0) /\
        0 < sigma /\
        (!n. integrable p (\x. Normal ((X n x) pow 2))) /\
        (!n. variance p (Normal o X n) = Normal (sigma pow 2)) /\
        (!n s. s IN subsets borel ==> distribution p (X n) s = mu s) /\
        (!n x. S n x = SIGMA (\i. X i x) (count n))
        ==>
        !f. f IN bounded_continuous euclidean ==>
            (((\n.
                 integral
                   (space borel, subsets borel,
                    distribution p
                      (\x. S n x / sqrt (&n * sigma pow 2)))
                   (Normal o f)) -->
              integral
                (space borel, subsets borel, std_normal_measure)
                (Normal o f))
             sequentially)``;

val central_limit_theorem =
  ``!(p : 'a p_space) (X : num -> 'a -> real)
      (mu : real measure) (sigma m : real) (S : num -> 'a -> real).
      let std_normal_density =
        \x : real. (1 / sqrt (2 * pi)) * exp (-(x pow 2) / 2)
      in
      let std_normal_measure =
        density_measure lborel (Normal o std_normal_density)
      in
        prob_space p /\
        measure_space (space borel, subsets borel, mu) /\
        (!n. random_variable (X n) p borel) /\
        indep_vars p X (\i. borel) UNIV /\
        (!n. expectation p (Normal o X n) = Normal m) /\
        0 < sigma /\
        (!n. integrable p (\x. Normal ((X n x) pow 2))) /\
        (!n. variance p (Normal o X n) = Normal (sigma pow 2)) /\
        (!n s. s IN subsets borel ==> distribution p (X n) s = mu s)
        ==>
        !f. f IN bounded_continuous euclidean ==>
            (((\n.
                 integral
                   (space borel, subsets borel,
                    distribution p
                      (\x.
                         SIGMA (\i. X i x - m) (count n) /
                         sqrt (&n * sigma pow 2)))
                   (Normal o f)) -->
              integral
                (space borel, subsets borel, std_normal_measure)
                (Normal o f))
             sequentially)``;
