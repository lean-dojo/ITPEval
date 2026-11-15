(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a4
  (putnambench__hol-light__putnam_2024_a4): classification of primes greater
  than 5 whose powers can be rearranged so that consecutive differences are
  a fixed positive residue modulo the prime; the unique prime is 7. This file
  contains no proof.
*)

let statement =
  `{p:num |
      prime p /\
      5 < p /\
      ?a r:int.
        &1 <= r /\
        r <= (&p:int) - &1 /\
        ?e:num->num.
          BIJ e (0..p-5) (0..p-5) /\
          !n:num.
            1 <= n /\ n <= p - 5
            ==>
            (&p:int) divides
              (a pow (e n) - a pow (e (n - 1)) - r)} =
   {p:num | p = 7}`;;
