(*
  Statement-only formalization of PutnamBench artifact putnam_1964_a6:
  for a finite set of real point coordinates with every nonmaximal pairwise
  distance repeated, all ratios of distinct pair distances are rational.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory pred_setTheory realTheory intrealTheory;

val putnam_1964_a6 =
  ``let pairs =
      \S : real set.
        {p : real # real |
           FST p IN S /\ SND p IN S /\ FST p < SND p}
    in
      let distance =
        \p : real # real. SND p - FST p
      in
        !S : real set.
          FINITE S /\
          (!p : real # real.
             p IN pairs S
             ==>
             ((?m : real # real.
                 m IN pairs S /\ distance m > distance p)
              ==>
              ?q : real # real.
                q IN pairs S /\
                q <> p /\
                distance p = distance q))
          ==>
          !p q : real # real.
            p IN pairs S /\
            q IN pairs S /\
            q <> p
            ==>
            ?n d : int.
              d <> 0 /\
              distance p / distance q =
                real_of_int n / real_of_int d``;
