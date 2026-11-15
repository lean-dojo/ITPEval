(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_a2:
  the ratio of the greatest positive integer satisfying a binomial-coefficient
  inequality to its positive index converges to (3 + sqrt 5) / 2. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory realTheory real_topologyTheory
     transcTheory;

val putnam_2016_a2 =
  ``!M : num -> num.
      (!n : num.
         0 < n
         ==>
         0 < M n /\
         binomial (M n - 1) n < binomial (M n) (n - 1) /\
         (!m : num.
            0 < m /\
            binomial (m - 1) n < binomial m (n - 1)
            ==>
            m <= M n))
      ==>
      let solution = ((3 + sqrt 5) / 2 : real)
      in
        (((\n : num. (&(M n) : real) / &n) --> solution)
         sequentially)``;
