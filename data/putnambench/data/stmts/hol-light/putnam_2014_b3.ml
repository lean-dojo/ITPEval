(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_b3:
  a rational matrix with at least the sum of its dimensions many distinct
  prime absolute entry values has rank at least two. This file contains no
  proof.
*)

let statement =
  `let is_rational =
     \x:real. ?a b:num. ~(b = 0) /\ abs x = &a / &b in
   let is_prime =
     \p:num.
       2 <= p /\
       !d:num. d divides p ==> d = 1 \/ d = p in
   !m n:num. !A:real^N^M.
     0 < m /\
     0 < n /\
     dimindex(:M) = m /\
     dimindex(:N) = n /\
     (!i j:num.
        i IN 1..m /\ j IN 1..n
        ==> is_rational(A$i$j)) /\
     m + n <=
       CARD
         {p:num |
            is_prime p /\
            ?i j:num.
              i IN 1..m /\
              j IN 1..n /\
              abs(A$i$j) = &p}
     ==> ?i1 i2 j1 j2:num.
           i1 IN 1..m /\
           i2 IN 1..m /\
           j1 IN 1..n /\
           j2 IN 1..n /\
           ~(i1 = i2) /\
           ~(j1 = j2) /\
           ~(A$i1$j1 * A$i2$j2 - A$i1$j2 * A$i2$j1 = &0)`;;
