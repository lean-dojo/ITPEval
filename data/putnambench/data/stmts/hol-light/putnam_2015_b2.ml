(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_b2:
  the iterative process deleting the three smallest positive integers still
  present and their sum produces a sum ending in the decimal digits 2015.
  This file contains no proof.
*)

let statement =
  `!sets:num->num->bool.
   !min1 min2 min3:(num->bool)->num.
   !sums:num->num.
     sets 0 = {k:num | 1 <= k} /\
     (!S:num->bool.
        (?a b c:num.
           a IN S /\
           b IN S /\
           c IN S /\
           ~(a = b) /\
           ~(a = c) /\
           ~(b = c))
        ==>
        min1 S IN S /\
        (!x:num. x IN S ==> min1 S <= x) /\
        min2 S IN (S DELETE min1 S) /\
        (!x:num. x IN (S DELETE min1 S) ==> min2 S <= x) /\
        min3 S IN ((S DELETE min1 S) DELETE min2 S) /\
        (!x:num.
           x IN ((S DELETE min1 S) DELETE min2 S)
           ==> min3 S <= x)) /\
     (!n:num. sums n = min1 (sets n) + min2 (sets n) + min3 (sets n)) /\
     (!n:num.
        sets (n + 1) =
        ((((sets n DELETE min1 (sets n)) DELETE min2 (sets n))
           DELETE min3 (sets n))
          DELETE sums n))
     ==>
     ((?n:num. sums n MOD 10000 = 2015) <=> T)`;;
