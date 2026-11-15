(*
  Statement-only formalization of PutnamBench artifact putnam_1974_a3:
  classification modulo 8 of the odd primes represented by each of two
  positive binary quadratic forms. This file contains no proof.
*)

let statement =
  `let solution =
     ({p:num | prime p /\ p MOD 8 = 1},
      {p:num | prime p /\ p MOD 8 = 5}) in
   (!p:num.
      prime p /\ p > 2
      ==> ((?m n:int. &p = m pow 2 + n pow 2) <=>
           p MOD 4 = 1))
   ==>
   !p:num.
     ((prime p /\ p > 2 /\
       (?x y:int. &p = x pow 2 + &16 * y pow 2)) <=>
      p IN FST solution) /\
     ((prime p /\ p > 2 /\
       (?x y:int.
          &p = &4 * x pow 2 + &4 * x * y + &5 * y pow 2)) <=>
      p IN SND solution)`;;
