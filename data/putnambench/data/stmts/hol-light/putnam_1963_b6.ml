(*
  Statement-only formalization of PutnamBench artifact putnam_1963_b6:
  stabilization after two iterations of taking all closed line segments
  between pairs of points in a nonempty Euclidean set of dimension at most three.
  This file contains no proof.
*)

let statement =
  `!S A.
     S = (\s:real^N->bool.
            {x | ?p q u.
                   p IN s /\ q IN s /\
                   &0 <= u /\ u <= &1 /\
                   !i. 1 <= i /\ i <= dimindex(:N)
                       ==> x$i = (&1 - u) * p$i + u * q$i}) /\
     1 <= dimindex(:N) /\ dimindex(:N) <= 3 /\
     ~(A 0 = {}) /\
     (!n. 1 <= n ==> A n = S (A (n - 1)))
     ==> !n. 2 <= n ==> A n = A (n + 1)`;;
