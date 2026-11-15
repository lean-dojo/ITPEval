(*
  Statement-only formalization of PutnamBench artifact putnam_1969_a2:
  the determinant of the n by n real matrix with entries equal to the
  absolute differences of their row and column indices. This file contains no proof.
*)

let statement =
  `let D = \i j:num. abs (&i - &j) in
   let ndet =
     \(A:num->num->real) n.
       sum {p:num->num |
              BIJ p (0..n-1) (0..n-1) /\
              (!i:num. ~(i IN 0..n-1) ==> p i = i)}
           (\p.
              (if EVEN
                    (CARD
                      {(i,j) |
                         i < n /\ j < n /\ i < j /\ p j < p i})
               then &1
               else -- &1) *
              product (0..n-1) (\i. A i (p i))) in
   !n:num.
     2 <= n
     ==> ndet D n =
         (-- &1) pow (n-1) * &(n-1) * (&2 pow (n-2))`;;
