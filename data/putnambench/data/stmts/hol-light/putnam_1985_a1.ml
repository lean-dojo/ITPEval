(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_a1:
  the number of ordered triples of sets with union {1,...,10} and empty
  common intersection, expressed by its prime exponents. This file contains
  no proof.
*)

let statement =
  `let putnam_1985_a1_solution = (10,10,0,0) in
   let a = FST putnam_1985_a1_solution in
   let b = FST (SND putnam_1985_a1_solution) in
   let c = FST (SND (SND putnam_1985_a1_solution)) in
   let d = SND (SND (SND putnam_1985_a1_solution)) in
   CARD
     {(A1,A2,A3):(num->bool)#(num->bool)#(num->bool) |
        A1 UNION A2 UNION A3 = 1..10 /\
        A1 INTER A2 INTER A3 = {}} =
   2 EXP a * 3 EXP b * 5 EXP c * 7 EXP d`;;
