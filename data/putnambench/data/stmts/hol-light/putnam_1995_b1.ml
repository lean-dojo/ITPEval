(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_b1:
  two partitions of a nine-element set have two distinct elements whose
  containing parts have equal sizes in both partitions. This file contains no
  proof.
*)

let statement =
  `let is_partition =
     \(P:(num->bool)->bool).
       FINITE P /\
       (!part:num->bool.
          part IN P
          ==> FINITE part /\
              ~(part = {}) /\
              part SUBSET (1..9)) /\
       UNIONS P = (1..9) /\
       (!part1 part2:num->bool.
          part1 IN P /\ part2 IN P /\ ~(part1 = part2)
          ==> DISJOINT part1 part2) in
   let part_size =
     \(P:(num->bool)->bool) (x:num).
       CARD (@part:num->bool. part IN P /\ x IN part) in
   !P1 P2:(num->bool)->bool.
     is_partition P1 /\ is_partition P2
     ==> ?x y:num.
       x IN (1..9) /\
       y IN (1..9) /\
       ~(x = y) /\
       part_size P1 x = part_size P1 y /\
       part_size P2 x = part_size P2 y`;;
