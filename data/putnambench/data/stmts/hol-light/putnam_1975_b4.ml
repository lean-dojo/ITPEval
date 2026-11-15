(*
  Statement-only formalization of PutnamBench artifact putnam_1975_b4:
  the nonexistence of a topologically closed subset of the real unit circle
  containing exactly one point from each antipodal pair. This file contains
  no proof.
*)

let statement =
  `let P =
     \(p:real#real).
       (FST p) pow 2 + (SND p) pow 2 = &1 in
   let closed_plane =
     \B:(real#real)->bool.
       !p:real#real.
         ~(p IN B)
         ==> ?e:real.
               &0 < e /\
               !q:real#real.
                 (FST q - FST p) pow 2 +
                 (SND q - SND p) pow 2 < e pow 2
                 ==> ~(q IN B) in
   let putnam_1975_b4_solution = F in
   ((?B:(real#real)->bool.
       B SUBSET {p:real#real | P p} /\
       closed_plane B /\
       !x y:real.
         P (x,y)
         ==> ~(((x,y) IN B) <=> ((--x,--y) IN B))) <=>
    putnam_1975_b4_solution)`;;
