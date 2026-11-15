(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_b4
  (putnambench__hol-light__putnam_2016_b4): the expected determinant of
  A - transpose A for a uniformly random 2n by 2n zero-one matrix.
  This file contains no proof.
*)

let statement =
  `let ndet =
     \(A:num->num->real) m.
       sum {p:num->num |
              BIJ p (1..m) (1..m) /\
              (!i:num. ~(i IN 1..m) ==> p i = i)}
           (\p.
              (if EVEN
                    (CARD
                      {(i,j) |
                         i IN 1..m /\ j IN 1..m /\
                         i < j /\ p j < p i})
               then &1
               else -- &1) *
              product (1..m) (\i. A i (p i))) in
   let mats01 =
     \m:num.
       {A:num->num->real |
          !i j:num.
            if i IN 1..m /\ j IN 1..m
            then A i j = &0 \/ A i j = &1
            else A i j = &0} in
   !n:num.
     1 <= n
     ==>
     sum (mats01 (2 * n))
       (\A. ndet (\i j. A i j - A j i) (2 * n)) /
       &(CARD (mats01 (2 * n))) =
     &(FACT (2 * n)) / ((&4) pow n * &(FACT n))`;;
