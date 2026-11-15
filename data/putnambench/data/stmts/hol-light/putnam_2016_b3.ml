(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_b3
  (putnambench__hol-light__putnam_2016_b3): a finite planar point set whose
  vertex triangles all have area at most 1 is contained in a triangle of area
  exactly 4. This file contains no proof.
*)

let statement =
  `let triangle_area =
     \A B C:real^2.
       abs ((B$1 - A$1) * (C$2 - A$2) -
            (B$2 - A$2) * (C$1 - A$1)) / &2 in
   let in_closed_triangle =
     \A B C P:real^2.
       ?u v w:real.
         &0 <= u /\ &0 <= v /\ &0 <= w /\
         u + v + w = &1 /\
         P$1 = u * A$1 + v * B$1 + w * C$1 /\
         P$2 = u * A$2 + v * B$2 + w * C$2 in
   !S:(real^2)->bool.
     FINITE S /\
     (!A B C:real^2.
        A IN S /\ B IN S /\ C IN S
        ==> triangle_area A B C <= &1)
     ==>
     ?A' B' C':real^2.
       triangle_area A' B' C' = &4 /\
       (!P:real^2. P IN S ==> in_closed_triangle A' B' C' P)`;;
