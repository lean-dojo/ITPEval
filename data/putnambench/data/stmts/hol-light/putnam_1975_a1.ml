(*
  Statement-only formalization of PutnamBench artifact putnam_1975_a1:
  the integer correspondence between sums of two triangular numbers and
  representations of 4n + 1 as a sum of two squares, with an explicit
  transformation of witnesses. This file contains no proof.
*)

let statement =
  `let solution =
     ((\a b:int. a + b + &1),(\a b:int. a - b)) in
   let nab =
     \n a b:int.
       (&2:int) * n = a pow 2 + a + b pow 2 + b in
   let nxy =
     \n x y:int.
       (&4:int) * n + &1 = x pow 2 + y pow 2 in
   (!n a b:int.
      nab n a b <=>
      nxy n ((FST solution) a b) ((SND solution) a b)) /\
   (!n:int.
      (?x y:int. nxy n x y)
      ==> ?a b:int. nab n a b)`;;
