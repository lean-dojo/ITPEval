(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_b5
  (putnambench__hol-light__putnam_2019_b5): the unique positive Fibonacci
  indices whose difference equals the value at 2019 of the degree-1008 real
  polynomial interpolating the prescribed odd-index values. This file
  contains no proof.
*)

let statement =
  `let eval_poly =
     \(p:real list) (x:real).
       ITLIST (\a acc. a + x * acc) p (&0) in
   !f:num->int. !p:real list.
     (!x:num.
        1 <= x
        ==> f (x + 2) = f (x + 1) + f x) /\
     f 1 = &1 /\
     f 2 = &1 /\
     LENGTH p = 1009 /\
     ~(LAST p = &0) /\
     (!n:num.
        n <= 1008
        ==> eval_poly p (&(2 * n + 1)) =
            real_of_int (f (2 * n + 1)))
     ==>
     !j k:num.
       (eval_poly p (&2019) = real_of_int (f j - f k) /\
        1 <= j /\
        1 <= k)
       <=>
       (j,k) = (2019,1010)`;;
