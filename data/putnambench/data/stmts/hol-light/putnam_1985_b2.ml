(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_b2:
  the explicit prime-power factorization of f_100(1) for a recursively
  differentiated sequence of real polynomials. This file contains no proof.
*)

let statement =
  `let has_derivative_at =
     \(g:real->real) (d:real) (x:real).
       !e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real.
                 &0 < abs (y - x) /\ abs (y - x) < delta
                 ==> abs ((g y - g x) / (y - x) - d) < e in
   !f:num->real->real.
     (!n:num. polynomial_function (f n)) /\
     f 0 = (\x:real. &1) /\
     (!n:num. 1 <= n ==> f n (&0) = &0) /\
     (!n:num. !x:real.
        has_derivative_at (f (n + 1)) (&(n + 1) * f n (x + &1)) x)
     ==> prime 101 /\
         f 100 (&1) = &(101 EXP 99)`;;
