(*
  Statement-only formalization of PutnamBench artifact putnam_1978_b3:
  the largest real roots of the recursively defined polynomial sequence are
  strictly increasing and converge to zero. This file contains no proof.
*)

let statement =
  `!P:num->real->real a:num->real.
     (!x:real. P 1 x = &1 + x) /\
     (!x:real. P 2 x = &1 + &2 * x) /\
     (!n:num.
        1 <= n
        ==>
        !x:real.
          P (2 * n + 1) x =
          P (2 * n) x + &(n + 1) * x * P (2 * n - 1) x) /\
     (!n:num.
        1 <= n
        ==>
        !x:real.
          P (2 * n + 2) x =
          P (2 * n + 1) x + &(n + 1) * x * P (2 * n) x) /\
     (!n:num. 1 <= n ==> P n (a n) = &0) /\
     (!n:num.
        1 <= n
        ==> !x:real. P n x = &0 ==> x <= a n)
     ==>
     (!i j:num. 1 <= i /\ i < j ==> a i < a j) /\
     (!e:real.
        &0 < e
        ==> ?N:num.
              !n:num. N <= n ==> abs (a n) < e)`;;
