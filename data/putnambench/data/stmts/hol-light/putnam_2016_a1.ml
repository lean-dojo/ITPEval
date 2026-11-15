(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_a1:
  the least positive derivative order, namely 8, for which every
  integer-coefficient polynomial evaluates to a multiple of 2016 after that
  many formal derivatives at every integer input. This file contains no proof.
*)

needs "Library/iter.ml";;

let statement =
  `let eval =
     \p:int list. \x:int.
       ITLIST (\c acc. c + x * acc) p (&0) in
   let diff =
     \p:int list.
       (list_of_seq
          (\i:num. &(i + 1) * EL (i + 1) p)
          (PRE (LENGTH p)):int list) in
   let admissible =
     \j:num.
       !p:int list. !k:int.
         (&2016:int) divides eval (ITER j diff p) k in
   0 < 8 /\
   admissible 8 /\
   (!j:num. 0 < j /\ admissible j ==> 8 <= j)`;;
