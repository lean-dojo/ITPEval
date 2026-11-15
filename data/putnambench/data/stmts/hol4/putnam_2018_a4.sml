(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_a4:
  a coprime floor-difference word equal to the identity in an arbitrary group
  forces its two group elements to commute. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory integerTheory intrealTheory realTheory
     listTheory groupTheory;

val putnam_2018_a4 =
  ``!(grp : 'a group) (m n : num) (a : num -> int) (g h : 'a).
      let int_pow =
        \(x : 'a) (z : int).
          if 0 <= z then grp.exp x (Num z)
          else grp.exp (grp.inv x) (Num (-z))
      in
        Group grp /\
        g IN grp.carrier /\
        h IN grp.carrier /\
        0 < m /\
        0 < n /\
        gcd m n = 1 /\
        (!k : num.
           1 <= k /\ k <= n
           ==>
           a k =
             INT_FLOOR ((&(m * k) : real) / (&n : real)) -
             INT_FLOOR ((&(m * (k - 1)) : real) / (&n : real))) /\
        FOLDL
          grp.op
          grp.id
          (GENLIST
             (\i : num. grp.op g (int_pow h (a (SUC i))))
             n) =
        grp.id
        ==>
        grp.op g h = grp.op h g``;
