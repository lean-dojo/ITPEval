(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a3
  (putnambench__hol-light__putnam_2024_a3): existence of two grid positions
  for which between one third and two thirds of the admissible increasing
  bijections order their entries in the specified direction. This file
  contains no proof.
*)

let statement =
  `let rows = 1..3 in
   let columns = 1..2024 in
   let grid = {(i,j) | i IN rows /\ j IN columns} in
   let values = 1..6072 in
   let admissible =
     \(t:num#num->num).
       BIJ t grid values /\
       (!j:num.
          j IN columns
          ==> !i k:num.
                i IN rows /\ k IN rows /\ i < k
                ==> t (i,j) < t (k,j)) /\
       (!i:num.
          i IN rows
          ==> !j k:num.
                j IN columns /\ k IN columns /\ j < k
                ==> t (i,j) < t (i,k)) /\
       (!p:num#num. ~(p IN grid) ==> t p = 0) in
   let S = {t:num#num->num | admissible t} in
   ?a b c d:num.
     a IN rows /\
     b IN columns /\
     c IN rows /\
     d IN columns /\
     &1 / &3 <=
       &(CARD {t:num#num->num | t IN S /\ t (a,b) < t (c,d)}) /
       &(CARD S) /\
     &(CARD {t:num#num->num | t IN S /\ t (a,b) < t (c,d)}) /
       &(CARD S) <=
     &2 / &3`;;
