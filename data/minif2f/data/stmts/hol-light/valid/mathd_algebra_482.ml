(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_482. This file contains no
  proof.
*)

(*
  miniF2F valid artifact mathd_algebra_482: distinct natural primes m and n
  are roots of the real quadratic x^2 - 12x + k, forcing k = 35.
  This is a statement-only formalization and contains no proof.
*)

let statement =
  `!m n:num k:real f:real->real.
     prime m /\
     prime n /\
     (!x:real. f x = x pow 2 - &12 * x + k) /\
     f (&m) = &0 /\
     f (&n) = &0 /\
     ~(m = n)
     ==> k = &35`;;
