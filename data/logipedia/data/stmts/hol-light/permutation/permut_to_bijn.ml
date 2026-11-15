(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.permut_to_bijn, catalog title "permutation.permut_to_bijn":
  every injective self-map of the natural numbers through a fixed bound is
  surjective on that bounded initial segment. This file contains no proof.
*)

let statement =
  `!n:num.
   !f:num->num.
     ((!i:num.
         i <= n
         ==> f i <= n) /\
      (!i j:num.
         i <= n
         ==> j <= n
         ==> f i = f j
         ==> i = j))
     ==> (!m:num.
            m <= n
            ==> ?p:num. p <= n /\ f p = m)`;;
