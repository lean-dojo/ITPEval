(*
  Statement-only formalization of PutnamBench artifact putnam_2021_a3
  (putnambench__hol-light__putnam_2021_a3): positive integers N for which
  x^2 + y^2 + z^2 = N contains an inscribed regular tetrahedron with
  integer-coordinate vertices. This file contains no proof.
*)

let statement =
  `let squared_distance =
     \(P:real^3) (Q:real^3).
       (P$1 - Q$1) pow 2 +
       (P$2 - Q$2) pow 2 +
       (P$3 - Q$3) pow 2 in
   let integer_coordinates =
     \(P:real^3).
       ?x y z:int.
         P$1 = real_of_int x /\
         P$2 = real_of_int y /\
         P$3 = real_of_int z in
   let on_sphere =
     \N:num. \(P:real^3).
       P$1 pow 2 + P$2 pow 2 + P$3 pow 2 = &N in
   let regular_integer_tetrahedron =
     \N:num.
       ?A B C D:real^3.
         on_sphere N A /\
         on_sphere N B /\
         on_sphere N C /\
         on_sphere N D /\
         integer_coordinates A /\
         integer_coordinates B /\
         integer_coordinates C /\
         integer_coordinates D /\
         &0 < squared_distance A B /\
         squared_distance A B = squared_distance A C /\
         squared_distance A B = squared_distance A D /\
         squared_distance A B = squared_distance B C /\
         squared_distance A B = squared_distance B D /\
         squared_distance A B = squared_distance C D in
   !N:num.
     (0 < N /\ regular_integer_tetrahedron N) <=>
     (?m:num. 0 < m /\ N = 3 * m EXP 2)`;;
