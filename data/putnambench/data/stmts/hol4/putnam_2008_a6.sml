(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_a6:
  a universal logarithmic-length sequence in every nontrivial finite group
  whose order-preserving subsequence products cover the group. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory transcTheory
     groupTheory;

val putnam_2008_a6 =
  ``?c : real.
      0 < c /\
      !(g : 'a group).
        FiniteGroup g /\
        1 < CARD g.carrier
        ==>
        ?s : 'a list.
          (!x : 'a. MEM x s ==> x IN g.carrier) /\
          (&(LENGTH s) : real) <= c * ln (&(CARD g.carrier) : real) /\
          !x : 'a.
            x IN g.carrier
            ==>
            ?indices : num list.
              (!i : num.
                 i < LENGTH indices
                 ==>
                 EL i indices < LENGTH s) /\
              (!i j : num.
                 i < j /\ j < LENGTH indices
                 ==>
                 EL i indices < EL j indices) /\
              FOLDR g.op g.id (MAP (\i : num. EL i s) indices) = x``;
