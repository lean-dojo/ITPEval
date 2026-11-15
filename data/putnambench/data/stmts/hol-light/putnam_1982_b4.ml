(*
  Statement-only formalization of PutnamBench artifact putnam_1982_b4:
  truth of both claims about finite nonempty sets of distinct integers whose
  product divides the product of every integer translate. This file contains
  no proof.
*)

let statement =
  `let admissible =
     \n:int->bool.
       FINITE n /\
       ~(n = {}) /\
       (!k:int.
          iproduct n (\i:int. i) divides
          iproduct n (\i:int. i + k)) in
   let putnam_1982_b4_solution = (T,T) in
   (((!n:int->bool.
        admissible n
        ==> (&1:int) IN n \/ --(&1:int) IN n) <=>
     FST putnam_1982_b4_solution) /\
    ((!n:int->bool.
        admissible n /\
        (!i:int. i IN n ==> (&0:int) < i)
        ==> n = {i:int | (&1:int) <= i /\ i <= &(CARD n)}) <=>
     SND putnam_1982_b4_solution))`;;
