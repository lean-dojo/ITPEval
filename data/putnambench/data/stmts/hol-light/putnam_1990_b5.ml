(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_b5:
  existence of a nonzero real coefficient sequence whose degree-n truncation
  has exactly n distinct real roots for every positive n. This file contains
  no proof.
*)

let statement =
  `let putnam_1990_b5_solution = T in
   ((?a:num->real.
       (!i:num. ~(a i = &0)) /\
       (!n:num.
          1 <= n
          ==> FINITE
                {x:real |
                   sum (0..n) (\i. a i * x pow i) = &0} /\
              CARD
                {x:real |
                   sum (0..n) (\i. a i * x pow i) = &0} = n))
    <=> putnam_1990_b5_solution)`;;
