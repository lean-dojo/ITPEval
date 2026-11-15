(*
  Statement-only formalization of PutnamBench artifact putnam_1981_a5:
  the lower bound on the number of distinct real roots of a polynomial
  expression involving a real polynomial and its derivative. This file
  contains no proof.
*)

let statement =
  `let has_derivative_at =
     \(f:real->real) (d:real) (x:real).
       !e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real.
                 &0 < abs (y - x) /\ abs (y - x) < delta
                 ==> abs ((f y - f x) / (y - x) - d) < e in
   let deriv =
     \(f:real->real) (x:real). @d:real. has_derivative_at f d x in
   let Q =
     \(P:real->real) (x:real).
       (x pow 2 + &1) * P x * deriv P x +
       x * ((P x) pow 2 + (deriv P x) pow 2) in
   let real_ncard =
     \s:real->bool. if FINITE s then &(CARD s) else &0 in
   let n =
     \(P:real->real). real_ncard {x:real | x > &1 /\ P x = &0} in
   ((!P:real->real.
       polynomial_function P
       ==> real_ncard {x:real | Q P x = &0} >= &2 * n P - &1) <=>
    T)`;;
