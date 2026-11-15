(*
  Statement-only formalization of miniF2F test problem imosl_2007_algebra_p6:
  a strict cyclic cubic inequality for a normalized sequence of 100
  nonnegative real numbers. This file contains no proof.
*)

let imosl_2007_algebra_p6 =
  `!a:num->real.
      (!n. a n >= &0) /\
      sum (0..(100 - 1)) (\x. (a (x + 1)) pow 2) = &1
      ==>
      sum (0..(99 - 1))
        (\x. (a (x + 1)) pow 2 * a (x + 2)) +
      (a 100) pow 2 * a 1 < &12 / &25`;;
