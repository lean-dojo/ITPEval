(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_times_to_divides, catalog title
  "gcd.divides_times_to_divides": Euclid's lemma for natural numbers, stating
  that a prime divisor of a product divides at least one factor. This file
  contains no proof.
*)

let statement =
  `!p n m:num.
     prime p
     ==> p divides (n * m)
     ==> p divides n \/ p divides m`;;
