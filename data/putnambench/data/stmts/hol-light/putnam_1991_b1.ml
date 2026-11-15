(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_b1:
  classification of the positive initial values for which repeatedly adding
  the remainder after the greatest square produces an eventually constant
  sequence. This file contains no proof.
*)

let statement =
  `!m S a:num->num. !A:num.
     (!n:num.
        m n EXP 2 <= n /\
        (!r:num. r EXP 2 <= n ==> r <= m n)) /\
     (!n:num. S n = n - m n EXP 2) /\
     a 0 = A /\
     (!k:num. a (k + 1) = a k + S (a k)) /\
     0 < A
     ==>
     ((?K c:num. !k:num. K <= k ==> a k = c) <=>
      (?x:num. 0 < x /\ A = x EXP 2))`;;
