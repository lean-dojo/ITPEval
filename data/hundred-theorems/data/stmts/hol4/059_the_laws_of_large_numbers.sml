(*
  Statement-only formalization of "The Laws of Large Numbers" from Hundred
  Theorems item 059. It states the strong law for identically distributed,
  pairwise-independent integrable real-valued random variables: their running
  averages converge almost surely to their common expectation. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory iterateTheory realTheory;
open topologyTheory real_topologyTheory extrealTheory measureTheory borelTheory;
open lebesgueTheory lebesgue_measureTheory probabilityTheory;

val strong_law_of_large_numbers_iid =
  ``!(p : 'a p_space) (X : num -> 'a -> extreal).
      prob_space p /\
      (!n. real_random_variable (X n) p) /\
      pairwise_indep_vars p X (\n. Borel) UNIV /\
      identical_distribution p X Borel UNIV /\
      integrable p (X 0)
      ==>
      (((\n x. SIGMA (\i. X i x) (count1 n) / &SUC n) -->
        (\x. expectation p (X 0)))
       (almost_everywhere p))``;
