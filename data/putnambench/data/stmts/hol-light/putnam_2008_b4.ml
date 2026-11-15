(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_b4:
  injectivity of an integer polynomial modulo the square of a prime implies
  injectivity modulo its cube on the corresponding residue ranges. This file
  contains no proof.
*)

let statement =
  `let eval =
     \h:int list. \x:int.
       ITLIST (\c acc. c + x * acc) h (&0) in
   !p:num. !h:int list.
     prime p /\
     (!i j:num.
        i < p EXP 2 /\ j < p EXP 2 /\
        (eval h (&i) == eval h (&j)) (mod (&(p EXP 2):int))
        ==> i = j)
     ==>
     (!i j:num.
        i < p EXP 3 /\ j < p EXP 3 /\
        (eval h (&i) == eval h (&j)) (mod (&(p EXP 3):int))
        ==> i = j)`;;
