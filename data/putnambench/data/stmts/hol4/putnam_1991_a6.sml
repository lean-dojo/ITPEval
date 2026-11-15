(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_a6:
  equality between the number of strict-gap compositions of each positive
  integer and the number of ordered compositions using every required term
  of the recurrence 1, 2, 4, ... . This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory;

val putnam_1991_a6 =
  ``let nabsum =
      \n (ab : num # (num -> num)).
        1 <= FST ab /\
        (!i : num. i < FST ab ==> 0 < SND ab i) /\
        (!i : num. FST ab <= i ==> SND ab i = 0) /\
        SIGMA (SND ab) (count (FST ab)) = n
    in
    let agt =
      \a : num # (num -> num).
        (!i : num.
           i + 2 < FST a
           ==>
           SND a i > SND a (i + 1) + SND a (i + 2)) /\
        (1 < FST a
         ==>
         SND a (FST a - 2) > SND a (FST a - 1))
    in
    let A =
      \n : num.
        CARD
          {a : num # (num -> num) |
             nabsum n a /\ agt a}
    in
    let bge =
      \b : num # (num -> num).
        !i : num.
          i + 1 < FST b
          ==>
          SND b i >= SND b (i + 1)
    in
    let bg1 =
      \g (b : num # (num -> num)).
        !i : num.
          i < FST b
          ==>
          ?j : num. SND b i = g j
    in
    let bg2 =
      \g (b : num # (num -> num)).
        ?k : num.
          SND b 0 = g k /\
          !j : num.
            j <= k
            ==>
            ?i : num. i < FST b /\ SND b i = g j
    in
    let B =
      \g n.
        CARD
          {b : num # (num -> num) |
             nabsum n b /\ bge b /\ bg1 g b /\ bg2 g b}
    in
      !g : num -> num.
        (g 0 = 1 /\
         g 1 = 2 /\
         (!j : num.
            2 <= j
            ==>
            g j = g (j - 1) + g (j - 2) + 1))
        ==>
        !n : num. 1 <= n ==> A n = B g n``;
