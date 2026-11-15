(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_b2:
  the least possible distance AB among noncollinear lattice-point triangles
  with all three side lengths integral is 3. This file contains no proof.
*)

let statement =
  `let lattice_point =
     \(p:real#real).
       ?m n:int.
         FST p = real_of_int m /\ SND p = real_of_int n in
   let edist =
     \(p:real#real) (q:real#real).
       sqrt ((FST p - FST q) pow 2 + (SND p - SND q) pow 2) in
   let integral_distance =
     \(p:real#real) (q:real#real).
       ?n:int. edist p q = real_of_int n in
   let noncollinear =
     \(a:real#real) (b:real#real) (c:real#real).
       ~((FST b - FST a) * (SND c - SND a) =
         (SND b - SND a) * (FST c - FST a)) in
   let admissible =
     \(a:real#real) (b:real#real) (c:real#real).
       lattice_point a /\
       lattice_point b /\
       lattice_point c /\
       integral_distance a b /\
       integral_distance a c /\
       integral_distance b c /\
       noncollinear a b c in
   (?a b c:real#real.
      admissible a b c /\ edist a b = &3) /\
   (!a b c:real#real.
      admissible a b c ==> &3 <= edist a b)`;;
