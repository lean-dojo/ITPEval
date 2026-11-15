(*
  Statement-only formalization of PutnamBench artifact putnam_1977_a2:
  the nonzero real solutions of the sum and reciprocal-sum equations are
  exactly the three families where two inputs are negatives and the remaining
  input equals the output. This file contains no proof.
*)

let statement =
  `!a b c d:real.
     ~(a = &0) /\ ~(b = &0) /\ ~(c = &0) /\ ~(d = &0)
     ==> ((a + b + c = d /\
           &1 / a + &1 / b + &1 / c = &1 / d) <=>
          (d = a /\ b = --c) \/
          (d = b /\ a = --c) \/
          (d = c /\ a = --b))`;;
