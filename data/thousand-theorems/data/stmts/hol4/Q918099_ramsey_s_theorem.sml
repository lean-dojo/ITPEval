(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q918099, "Ramsey's theorem": every finite coloring of the r-element subsets
  of an infinite set of natural numbers has an infinite homogeneous subset.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val ramsey_r =
  ``!K : 'a set. !r : num. !M1 : num set. !c : num set -> 'a.
      FINITE K /\
      INFINITE M1 /\
      (!e : num set.
         FINITE e /\
         CARD e = r /\
         e SUBSET M1
         ==>
         c e IN K)
      ==>
      ?M2 : num set.
        M2 SUBSET M1 /\
        INFINITE M2 /\
        ?col : 'a.
          col IN K /\
          !i : num set.
            FINITE i /\
            CARD i = r /\
            i SUBSET M2
            ==>
            c i = col``;
