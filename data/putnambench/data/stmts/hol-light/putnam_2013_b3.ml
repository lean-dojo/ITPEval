(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_b3:
  every valuation on a nonempty union- and intersection-closed family of
  finite subsets with one-element descent is a sum of element weights.
  This file contains no proof.
*)

let statement =
  `!n:num. !P:(num->bool)->bool. !f:(num->bool)->real.
     ~(P = {}) /\
     (!S:num->bool. S IN P ==> S SUBSET (1..n)) /\
     (!S S':num->bool.
        S IN P /\ S' IN P
        ==> S UNION S' IN P /\ S INTER S' IN P) /\
     (!S:num->bool.
        S IN P /\ ~(S = {})
        ==> ?t:num->bool.
              t IN P /\ t PSUBSET S /\ CARD t + 1 = CARD S) /\
     f {} = &0 /\
     (!S S':num->bool.
        S IN P /\ S' IN P
        ==> f (S UNION S') = f S + f S' - f (S INTER S'))
     ==> ?r:num->real.
           !S:num->bool. S IN P ==> f S = sum S r`;;
