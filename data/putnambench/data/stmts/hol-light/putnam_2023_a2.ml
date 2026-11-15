(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_a2:
  the remaining real reciprocal interpolation points of an even-degree monic
  polynomial prescribed at nonzero integers. This file contains no proof.
*)

let statement =
  `let eval =
     \p:real list. \x:real.
       ITLIST (\c acc. c + x * acc) p (&0) in
   !n:num p:real list.
     0 < n /\
     EVEN n /\
     LENGTH p = 2 * n + 1 /\
     LAST p = &1 /\
     (!k:int.
        (&1:int) <= abs k /\ abs k <= &n
        ==> eval p (&1 / real_of_int k) = (real_of_int k) pow 2)
     ==>
     !x:real.
       (~(x = &0) /\
        eval p (&1 / x) = x pow 2 /\
        ~(?k:int.
            x = real_of_int k /\
            (&1:int) <= abs k /\
            abs k <= &n))
       <=>
       x = &1 / &(FACT n) \/ x = --(&1 / &(FACT n))`;;
