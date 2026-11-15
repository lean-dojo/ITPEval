(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_b3:
  the sum of determinants of the row-major digit matrices associated with all
  positive n-squared-digit decimal integers. This file contains no proof.
*)

let statement =
  `let integer_det =
     \(A:num->num->int) n.
       isum {p:num->num |
               BIJ p (0..n-1) (0..n-1) /\
               (!i:num. ~(i IN 0..n-1) ==> p i = i)}
            (\p.
               (if EVEN
                     (CARD
                       {(i,j) |
                          i < n /\ j < n /\ i < j /\ p j < p i})
                then (&1:int)
                else --(&1:int)) *
               iproduct (0..n-1) (\i. A i (p i))) in
   let digits_set =
     \n:num.
       {f:num->num |
          ~(f 0 = 0) /\
          (!i:num. i < n EXP 2 ==> f i <= 9) /\
          (!i:num. n EXP 2 <= i ==> f i = 0)} in
   let digits_to_matrix =
     \n:num. \f:num->num. \i j:num. (&(f (i * n + j)):int) in
   let putnam_1995_b3_solution =
     \n:num.
       if n = 1 then (&45:int)
       else if n = 2 then (&10:int) * ((&45:int) pow 2)
       else &0 in
   !n:num.
     0 < n
     ==> isum (digits_set n)
              (\f. integer_det (digits_to_matrix n f) n) =
         putnam_1995_b3_solution n`;;
