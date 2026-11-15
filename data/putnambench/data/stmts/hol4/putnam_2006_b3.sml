(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_b3:
  the maximum number of unordered two-part partitions of an n-point planar
  set separated by a disjoint straight line is binomial n 2 + 1. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory pairTheory pred_setTheory realTheory;

val putnam_2006_b3 =
  ``!n : num.
      0 < n
      ==>
      let is_linear_partition =
        \(S : (real # real) set)
         (AB : ((real # real) set) set).
          CARD AB = 2 /\
          ?A B : (real # real) set.
            A IN AB /\
            B IN AB /\
            A <> B /\
            A UNION B = S /\
            DISJOINT A B /\
            ?m b : real.
              (!p : real # real.
                 p IN A ==> SND p > m * FST p + b) /\
              (!p : real # real.
                 p IN B ==> SND p < m * FST p + b)
      in
      let linear_partition_count =
        \S : (real # real) set.
          CARD
            {AB : ((real # real) set) set |
               is_linear_partition S AB}
      in
        (?S : (real # real) set.
           FINITE S /\
           CARD S = n /\
           linear_partition_count S = binomial n 2 + 1) /\
        (!S : (real # real) set.
           FINITE S /\
           CARD S = n
           ==>
           linear_partition_count S <= binomial n 2 + 1)``;
