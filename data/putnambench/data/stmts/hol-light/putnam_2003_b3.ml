(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_b3:
  the factorial of a positive integer as a product of least common multiples
  of initial integer intervals determined by quotients. This file contains no
  proof.
*)

let statement =
  `!n:num.
     0 < n
     ==> FACT n =
         nproduct (1..n)
           (\i:num.
              ITSET (\x acc:num. lcm(x,acc)) (1..(n DIV i)) 1)`;;
