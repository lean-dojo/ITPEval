(*
  Statement-only formalization of miniF2F valid problem amc12a_2020_p21. This file contains no
  proof.
*)

(*
  miniF2F amc12a_2020_p21: the natural numbers divisible by 5 that satisfy
  lcm(5!, n) = 5 * gcd(10!, n) form a set of cardinality 48.
  This is a statement-only formalization and contains no proof.
*)

let statement =
  `FINITE {n:num |
      5 divides n /\
      lcm (FACT 5,n) = 5 * gcd (FACT 10,n)} /\
   CARD {n:num |
      5 divides n /\
      lcm (FACT 5,n) = 5 * gcd (FACT 10,n)} = 48`;;
