(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a5
  (putnambench__hol-light__putnam_2025_a5): classification of the sign
  sequences that maximize the number of permutations with prescribed adjacent
  rises and falls. The maximizers are the two alternating sign sequences.
  This file contains no proof.
*)

let statement =
  `let admissible =
     \(n:num) (s:num->int).
       !i:num. i < n ==> s i = (&1:int) \/ s i = --(&1:int) in
   let permutation_count =
     \(n:num) (s:num->int).
       CARD
         {p:num->num |
            BIJ p (0..n) (0..n) /\
            (!i:num. n < i ==> p i = i) /\
            (!i:num.
               i < n
               ==> (&0:int) <
                   s i * ((&(p (i + 1)):int) - &(p i)))} in
   !n:num s:num->int.
     1 <= n /\ admissible n s
     ==>
     ((!t:num->int.
         admissible n t
         ==> permutation_count n t <= permutation_count n s)
      <=>
      ((!i:num.
          i < n
          ==> s i = if EVEN i then (&1:int) else --(&1:int)) \/
       (!i:num.
          i < n
          ==> s i = if EVEN i then --(&1:int) else (&1:int))))`;;
