(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_a2:
  the locus of midpoints of segments joining points on two circles with
  radii 1 and 3 whose centers are 10 units apart. This file contains no proof.
*)

let statement =
  `let edist =
     \(x:real#real) (y:real#real).
       sqrt ((FST x - FST y) pow 2 + (SND x - SND y) pow 2) in
   let midpoint =
     \(x:real#real) (y:real#real).
       ((FST x + FST y) / &2, (SND x + SND y) / &2) in
   !O1 O2:real#real.
     edist O1 O2 = &10
     ==>
     !M:real#real.
       ((?X Y:real#real.
           edist X O1 = &1 /\
           edist Y O2 = &3 /\
           M = midpoint X Y) <=>
        &1 <= edist M (midpoint O1 O2) /\
        edist M (midpoint O1 O2) <= &2)`;;
