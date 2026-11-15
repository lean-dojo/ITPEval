(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_b4
  (putnambench__hol-light__putnam_2018_b4): a real sequence initialized by
  1, a, a and satisfying the given third-order recurrence is periodic whenever
  one of its terms is zero. This file contains no proof.
*)

let statement =
  `!a:real. !x:num->real.
     (x 0 = &1 /\
      x 1 = a /\
      x 2 = a /\
      (!n:num.
         x (n + 3) =
         &2 * x (n + 2) * x (n + 1) - x n))
     ==>
     ((?n:num. x n = &0)
      ==>
      ?c:num.
        0 < c /\
        !n:num. x (n + c) = x n)`;;
