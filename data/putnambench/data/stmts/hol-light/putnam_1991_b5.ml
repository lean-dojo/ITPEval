(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_b5:
  the cardinality of the intersection of the quadratic residues modulo an odd
  prime with their translate by one. This file contains no proof.
*)

let statement =
  `let putnam_1991_b5_solution =
     \p:num. p DIV 4 + 1 in
   !p:num.
     ODD p /\ prime p
     ==>
     CARD
       ({z:num |
           z < p /\
           ?x:num. x < p /\ z = (x EXP 2) MOD p} INTER
        {z:num |
           z < p /\
           ?y:num. y < p /\ z = (y EXP 2 + 1) MOD p}) =
     putnam_1991_b5_solution p`;;
