(*
  Statement-only formalization of PutnamBench artifact putnam_1968_b5:
  the number of 2 by 2 matrices over residues modulo a prime with trace one
  and determinant zero. This file contains no proof.
*)

let statement =
  `!p:num.
     prime p
     ==> CARD
           {(a,b,c,d):num#num#num#num |
              a < p /\ b < p /\ c < p /\ d < p /\
              (a + d) MOD p = 1 /\
              (a * d) MOD p = (b * c) MOD p} =
         p EXP 2 + p`;;
