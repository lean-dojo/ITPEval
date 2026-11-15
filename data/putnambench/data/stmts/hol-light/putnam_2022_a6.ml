(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_a6
  (putnambench__hol-light__putnam_2022_a6): for 2*n ordered real points in
  (-1,1), the largest number of initial odd-power interval-sum identities
  that can simultaneously equal 1 is n. This file contains no proof.
*)

let statement =
  `let admissible =
     \n:num. \x:num->real.
       -- &1 < x 1 /\
       (!i:num.
          1 <= i /\ i < 2 * n
          ==> x i < x (i + 1)) /\
       x (2 * n) < &1 in
   let valid =
     \n:num. \m:num. \x:num->real.
       !k:num.
         1 <= k /\ k <= m
         ==>
         sum (1..n)
           (\i:num.
              x (2 * i) pow (2 * k - 1) -
              x (2 * i - 1) pow (2 * k - 1)) =
         &1 in
   let feasible =
     \n:num. \m:num.
       ?x:num->real. admissible n x /\ valid n m x in
   !n:num.
     0 < n
     ==>
     feasible n n /\
     (!m:num. feasible n m ==> m <= n)`;;
