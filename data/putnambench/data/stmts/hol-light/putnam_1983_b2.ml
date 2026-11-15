(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1983_b2:
  existence of a real polynomial whose floors count representations of each
  positive integer as a sum of powers of two, each used at most three times.
  This file contains no proof.
*)

let statement =
  `let floor_real =
     \x:real. @z:real. integer z /\ z <= x /\ x < z + &1 in
   let f =
     \n:num.
       CARD
         {c:num->num |
            FINITE {k:num | ~(c k = 0)} /\
            (!k:num. c k <= 3) /\
            nsum {k:num | ~(c k = 0)}
              (\k:num. c k * 2 EXP k) = n} in
   let putnam_1983_b2_solution = T in
   putnam_1983_b2_solution <=>
   (?a:num->real.
      FINITE {i:num | ~(a i = &0)} /\
      !n:num.
        0 < n
        ==> floor_real
              (sum {i:num | ~(a i = &0)}
                (\i:num. a i * (&n) pow i)) =
            &(f n))`;;
