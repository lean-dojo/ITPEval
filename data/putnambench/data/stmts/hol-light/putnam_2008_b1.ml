(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_b1:
  the maximum number of rational points on a circle in the real plane whose
  center is not a rational point is two. This file contains no proof.
*)

let statement =
  `let is_rational =
     \x:real.
       ?m n:int.
         ~(n = (&0:int)) /\
         x = real_of_int m / real_of_int n in
   let is_rational_point =
     \(p:real#real).
       is_rational (FST p) /\ is_rational (SND p) in
   let edist =
     \(p:real#real) (q:real#real).
       sqrt ((FST p - FST q) pow 2 + (SND p - SND q) pow 2) in
   let rational_points =
     \(c:real#real) (r:real).
       {p:real#real | edist p c = r /\ is_rational_point p} in
   (?c:real#real. ?r:real.
      ~is_rational_point c /\
      rational_points c r HAS_SIZE 2) /\
   (!c:real#real. !r:real.
      ~is_rational_point c
      ==> FINITE (rational_points c r) /\
          CARD (rational_points c r) <= 2)`;;
