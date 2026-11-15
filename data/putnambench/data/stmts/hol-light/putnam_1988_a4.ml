(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_a4:
  whether every coloring of the Euclidean plane with three, respectively
  nine, colors has a monochromatic pair at unit distance. This file contains
  no proof.
*)

let statement =
  `let edist =
     \(x:real#real) (y:real#real).
       sqrt ((FST x - FST y) pow 2 + (SND x - SND y) pow 2) in
   let p =
     \n:num.
       !color:(real#real)->num.
         (!v:real#real. color v < n)
         ==> ?x y:real#real.
               color x = color y /\ edist x y = &1 in
   let putnam_1988_a4_solution = (T,F) in
   (p 3 <=> FST putnam_1988_a4_solution) /\
   (p 9 <=> SND putnam_1988_a4_solution)`;;
