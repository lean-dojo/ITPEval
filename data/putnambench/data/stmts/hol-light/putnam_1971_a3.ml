(*
  Statement-only formalization of PutnamBench artifact putnam_1971_a3:
  three distinct lattice points on a circle of positive radius have side
  length product at least twice the radius. This file contains no proof.
*)

let statement =
  `let lattice_point =
     \(p:real#real).
       ?m n:int.
         FST p = real_of_int m /\ SND p = real_of_int n in
   let edist =
     \(p:real#real) (q:real#real).
       sqrt ((FST p - FST q) pow 2 + (SND p - SND q) pow 2) in
   !a b c:real#real. !R:real.
     lattice_point a /\ lattice_point b /\ lattice_point c /\
     ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
     &0 < R /\
     (?C:real#real.
        edist C a = R /\ edist C b = R /\ edist C c = R)
     ==> edist a b * edist a c * edist b c >= &2 * R`;;
