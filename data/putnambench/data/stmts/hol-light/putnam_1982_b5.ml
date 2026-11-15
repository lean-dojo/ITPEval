(*
  Statement-only formalization of PutnamBench artifact putnam_1982_b5:
  convergence of the iterated logarithm-base sequence for x greater than
  e^e and continuity of its real limit function. This file contains no proof.
*)

let statement =
  `let domain = {x:real | exp (exp (&1)) < x} in
   let converges_to =
     \(u:num->real) (l:real).
       !e:real.
         &0 < e
         ==> ?N:num.
               !n:num. N <= n ==> abs (u n - l) < e in
   let continuous_on =
     \(g:real->real) (s:real->bool).
       !x:real.
         x IN s
         ==> !e:real.
               &0 < e
               ==> ?d:real.
                     &0 < d /\
                     !y:real.
                       y IN s /\ abs (y - x) < d
                       ==> abs (g y - g x) < e in
   !S:real->num->real.
     (!x:real.
        x IN domain
        ==> S x 0 = exp (&1) /\
            (!n:num. S x (n + 1) = ln x / ln (S x n)))
     ==> (!x:real.
            x IN domain
            ==> ?L:real. converges_to (S x) L) /\
         (!g:real->real.
            (!x:real. x IN domain ==> converges_to (S x) (g x))
            ==> continuous_on g domain)`;;
