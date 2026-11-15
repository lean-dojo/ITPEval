(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_b1:
  every positive rational number is a quotient of finite products of
  factorials of primes. This file contains no proof.
*)

let statement =
  `let is_rational =
     \x:real.
       ?p:int q:num.
         ~(q = 0) /\
         x = real_of_int p / &q in
   let factorial_product =
     \ps:num list.
       ITLIST (\p acc. &(FACT p) * acc) ps (&1) in
   !q:real.
     is_rational q /\ &0 < q
     ==> ?numerator denominator:num list.
           (!p:num.
              MEM p (APPEND numerator denominator)
              ==> prime p) /\
           q =
           factorial_product numerator /
           factorial_product denominator`;;
