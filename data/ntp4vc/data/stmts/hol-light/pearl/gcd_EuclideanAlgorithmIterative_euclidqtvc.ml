(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/gcd_EuclideanAlgorithmIterative_euclidqtvc: the iterative Euclidean
  algorithm verification condition preserving nonnegativity and the integer
  greatest common divisor across a remainder step. This file contains no proof.
*)

let statement =
  `!u0 v0:int.
     (&0:int) <= u0
     ==>
     (&0:int) <= v0
     ==>
     (&0:int) <= u0 /\
     (&0:int) <= v0 /\
     (!v u:int.
        (((&0:int) <= u /\ (&0:int) <= v) /\
         gcd(u,v) = gcd(u0,v0))
        ==>
        (if ~(v = (&0:int)) then
           ~(v = (&0:int)) /\
           ((&0:int) <= v /\ u rem v < v) /\
           ((&0:int) <= v /\ (&0:int) <= u rem v) /\
           gcd(v,u rem v) = gcd(u0,v0)
         else
           u = gcd(u0,v0)))`;;
