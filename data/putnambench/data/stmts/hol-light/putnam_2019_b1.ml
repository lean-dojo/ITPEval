(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_b1:
  the number of four-point subsets of the prescribed integer lattice set
  whose elements are the vertices of a square is 5n + 1. This file contains
  no proof.
*)

let statement =
  `let pn =
     \n:num.
       {p:int#int |
          p = ((&0:int),(&0:int)) \/
          (?k:num.
             k <= n /\
             (FST p) pow 2 + (SND p) pow 2 = &(2 EXP k))} in
   let edist =
     \(p:int#int) (q:int#int).
       sqrt
         ((real_of_int (FST p) - real_of_int (FST q)) pow 2 +
          (real_of_int (SND p) - real_of_int (SND q)) pow 2) in
   let is_square =
     \(s:(int#int)->bool).
       ?a b c d:int#int.
         s = {a,b,c,d} /\
         s HAS_SIZE 4 /\
         (?e:real.
            &0 < e /\
            edist a b = e /\
            edist b c = e /\
            edist c d = e /\
            edist d a = e /\
            edist a c = edist b d) in
   !n:num.
     CARD
       {s:(int#int)->bool |
          s SUBSET pn n /\ is_square s} =
     5 * n + 1`;;
