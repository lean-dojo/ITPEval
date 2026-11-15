(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_a3:
  the probability that a uniformly ordered listing of 1 through 3k+1 has no
  prefix sum divisible by 3, together with its factorial closed form. This
  file contains no proof.
*)

let statement =
  `!k:num.
     0 < k
     ==>
     let n = 3 * k + 1 in
     let permutations =
       {p:num->num |
          BIJ p (1..n) (1..n) /\
          (!i:num. ~(i IN (1..n)) ==> p i = 0)} in
     let good_permutations =
       {p:num->num |
          p IN permutations /\
          (!j:num.
             j IN (1..n)
             ==> ~(3 divides nsum (1..j) p))} in
     &(CARD good_permutations) / &(CARD permutations) =
     &(FACT k) * &(FACT (k + 1)) /
     (&(3 * k + 1) * &(FACT (2 * k)))`;;
