(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527230,
  "Von Staudt–Clausen theorem": for every natural number k, the even Bernoulli
  number B_(2k) plus the sum of 1/p over primes p such that p - 1 divides 2k
  is an integer. This file contains no proof.
*)

needs "100/bernoulli.ml";;

let Q3527230_VON_STAUDT_CLAUSEN_THEOREM =
  `!k:num.
     integer
       (bernoulli (2 * k) +
        sum (0..(2 * k + 1))
          (\p. if prime p /\ (p - 1) divides (2 * k)
               then &1 / &p
               else &0))`;;
