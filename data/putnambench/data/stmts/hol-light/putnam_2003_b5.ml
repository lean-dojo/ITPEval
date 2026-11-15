(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2003_b5:
  a triangle whose side lengths are the distances from an interior point to
  the vertices of a unit-circle equilateral triangle has area depending only
  on the point's distance from the center. This file contains no proof.
*)

let statement =
  `let edist =
     \(p:real#real) (q:real#real).
       sqrt ((FST p - FST q) pow 2 + (SND p - SND q) pow 2) in
   let triangle_area =
     \(x:real#real) (y:real#real) (z:real#real).
       abs ((FST y - FST x) * (SND z - SND x) -
            (SND y - SND x) * (FST z - FST x)) / &2 in
   !A B C:real#real.
     edist (&0,&0) A = &1 /\
     edist (&0,&0) B = &1 /\
     edist (&0,&0) C = &1 /\
     edist A B = edist A C /\
     edist A B = edist B C /\
     ~(edist A B = &0)
     ==> ?f:real->real.
           !P:real#real.
             edist (&0,&0) P < &1
             ==> ?X Y Z:real#real.
                   edist X Y = edist P A /\
                   edist Y Z = edist P B /\
                   edist X Z = edist P C /\
                   triangle_area X Y Z = f (edist (&0,&0) P)`;;
