(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_b3:
  the largest cyclic adjacent-product sum over a permutation of {1,...,n} is
  (2n^3 + 3n^2 - 11n + 18) / 6 for n at least two. This file contains no proof.
*)

let statement =
  `!n:num.
     2 <= n
     ==>
     let admissible =
       \x:num->num. IMAGE x (0..n - 1) = (1..n) in
     let cyclic_sum =
       \x:num->num.
         nsum (0..n - 1) (\i. x i * x ((i + 1) MOD n)) in
     let putnam_1996_b3_solution =
       (2 * n EXP 3 + 3 * n EXP 2 + 18 - 11 * n) DIV 6 in
     (?x:num->num.
        admissible x /\
        cyclic_sum x = putnam_1996_b3_solution) /\
     (!x:num->num.
        admissible x
        ==> cyclic_sum x <= putnam_1996_b3_solution)`;;
