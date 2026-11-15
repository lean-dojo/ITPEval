(*
  Statement-only formalization of Thousand Theorems corpus artifact Q918099
  (thousand-theorems__hol-light__Q918099), "Ramsey's theorem": every coloring
  of the r-element subsets of an infinite set of natural numbers by finitely
  many colors has an infinite monochromatic subset. This file contains no
  proof.
*)

let Q918099_RAMSEY_S_THEOREM =
  `!K:A->bool. !r:num. !M1:num->bool. !c:(num->bool)->A.
     FINITE K /\
     INFINITE M1 /\
     (!e:num->bool.
        FINITE e /\ CARD e = r /\ e SUBSET M1
        ==> c e IN K)
     ==> ?M2:num->bool.
           M2 SUBSET M1 /\
           INFINITE M2 /\
           ?col:A.
             col IN K /\
             !i:num->bool.
               FINITE i /\ CARD i = r /\ i SUBSET M2
               ==> c i = col`;;
