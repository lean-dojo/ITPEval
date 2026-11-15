(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_b1:
  the minimum cardinality of the set of averages of two distinct elements
  of an n-element set of real numbers. This file contains no proof.
*)

let statement =
  `!n:num.
     2 <= n
     ==> let averages =
           \S:real->bool.
             {x:real | ?a b.
                a IN S /\ b IN S /\ ~(a = b) /\ (a + b) / &2 = x} in
         let attainable =
           {k:num | ?S:real->bool.
              S HAS_SIZE n /\ averages S HAS_SIZE k} in
         (2 * n - 3) IN attainable /\
         (!k. k IN attainable ==> 2 * n - 3 <= k)`;;
