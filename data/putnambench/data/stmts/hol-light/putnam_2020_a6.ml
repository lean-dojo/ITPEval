(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_a6
  (putnambench__hol-light__putnam_2020_a6): the least uniform upper bound for
  a family of finite odd-frequency trigonometric sums is pi divided by four.
  This file contains no proof.
*)

needs "Library/transc.ml";;

let statement =
  `let f =
     \N:num. \x:real.
       sum (0..N)
         (\n:num.
            ((&N + &1 / &2 - &n) /
             ((&N + &1) * (&2 * &n + &1))) *
            sin ((&2 * &n + &1) * x)) in
   (!N:num. !x:real.
      0 < N
      ==> f N x <= pi / &4) /\
   (!M:real.
      (!N:num. !x:real.
         0 < N
         ==> f N x <= M)
      ==> pi / &4 <= M)`;;
