(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.prime_to_not_divides_fact, catalog title
  "fermat.prime_to_not_divides_fact": a prime greater than a natural number
  does not divide that natural number's factorial. This file contains no
  proof.
*)

let statement =
  `!p:num.
     prime p
     ==> (!n:num.
            n < p
            ==> ~(p divides FACT n))`;;
