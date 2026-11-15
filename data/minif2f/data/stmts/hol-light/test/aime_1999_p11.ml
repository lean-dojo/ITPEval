(*
  Statement-only formalization of miniF2F artifact aime_1999_p11: a finite
  trigonometric sine sum determines a positive reduced rational angle whose
  numerator and denominator sum to 177. This file contains no proof.
*)

let statement =
  `!m n:num.
     0 < m /\
     0 < n /\
     gcd (m,n) = 1 /\
     m < 90 * n /\
     sum (1..35) (\k. sin (&5 * &k * pi / &180)) =
       tan ((&m / &n) * pi / &180)
     ==> m + n = 177`;;
