(*
  Statement-only formalization of PutnamBench artifact putnam_1978_b6:
  a quadratic bound for weighted finite double sums of real array entries
  lying in the interval [0,1]. This file contains no proof.
*)

let statement =
  `!a:num->num->real. !m n:num.
     (!i j:num. &0 <= a i j /\ a i j <= &1) /\
     0 < m /\
     0 < n
     ==>
     (sum (1..n)
        (\i:num. sum (1..(m * i)) (\j:num. a i j / &i))) pow 2
     <=
     &2 * &m *
     sum (1..n)
       (\i:num. sum (1..(m * i)) (\j:num. a i j))`;;
