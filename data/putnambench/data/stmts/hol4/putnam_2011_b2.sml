(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_b2:
  the primes occurring in at least seven prime-coefficient quadratic triples
  with a rational root are exactly 2 and 5. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory primeTheory ratTheory;

val putnam_2011_b2 =
  ``!S : (num # (num # num)) set. !t : num.
      S =
        {s : num # (num # num) |
           prime (FST s) /\
           prime (FST (SND s)) /\
           prime (SND (SND s)) /\
           ?x : rat.
             rat_of_num (FST s) * x * x +
               rat_of_num (FST (SND s)) * x +
               rat_of_num (SND (SND s)) =
             0q}
      ==>
      (prime t /\
       (?T : (num # (num # num)) set.
          FINITE T /\
          T SUBSET
            {s : num # (num # num) |
               s IN S /\
               (FST s = t \/
                FST (SND s) = t \/
                SND (SND s) = t)} /\
          7 <= CARD T)
       <=>
       t = 2 \/ t = 5)``;
