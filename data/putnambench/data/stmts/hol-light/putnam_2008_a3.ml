(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_a3:
  termination and choice-independent final sequence of the gcd/lcm replacement
  process on finite sequences of positive integers. This file contains no proof.
*)

let statement =
  `!n:num. !a:num->num.
     0 < n /\
     (!i:num. i < n ==> 0 < a i)
     ==>
     let cont =
       \(s:num->num).
         ?j k:num.
           j < n /\
           k < n /\
           j < k /\
           ~(s j divides s k) in
     let init =
       \(P:num->num->num).
         !i:num. i < n ==> P 0 i = a i in
     let trans =
       \(P:num->num->num).
         !t:num.
           cont (P t)
           ==>
           ?j k:num.
             j < n /\
             k < n /\
             j < k /\
             ~(P t j divides P t k) /\
             P (t + 1) j = gcd(P t j,P t k) /\
             P (t + 1) k = lcm(P t j,P t k) /\
             (!i:num.
                i < n /\
                ~(i = j) /\
                ~(i = k)
                ==> P (t + 1) i = P t i) in
     ?f:num->num.
       !P:num->num->num.
         init P
         ==> trans P
         ==> ?t:num.
               ~(cont (P t)) /\
               (!i:num. i < n ==> P t i = f i)`;;
