(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_a6:
  the number of ordered pairs of subsets of {1,...,10} whose elements each
  exceed the cardinality of the other subset. This file contains no proof.
*)

let statement =
  `CARD
     {(A,B):(num->bool)#(num->bool) |
        A SUBSET (1..10) /\
        B SUBSET (1..10) /\
        (!a:num. a IN A ==> CARD B < a) /\
        (!b:num. b IN B ==> CARD A < b)} =
   17711`;;
