(*
  Statement-only formalization of PutnamBench artifact putnam_1974_b4:
  pointwise approximation of every separately continuous real function on
  the plane by a sequence of continuous functions. This file contains no proof.
*)

let statement =
  `let continuous_real =
     \(h:real->real).
       !x e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !u:real. abs (u - x) < d ==> abs (h u - h x) < e in
   let continuous_plane =
     \(h:(real#real)->real).
       !x y e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !u v:real.
                 abs (u - x) < d /\ abs (v - y) < d
                 ==> abs (h (u,v) - h (x,y)) < e in
   let tends_pointwise =
     \(g:num->(real#real)->real) (f:(real#real)->real).
       !x y e:real.
         &0 < e
         ==> ?N:num.
               !n:num.
                 N <= n ==> abs (g n (x,y) - f (x,y)) < e in
   !f:(real#real)->real.
     (!y:real. continuous_real (\x:real. f (x,y))) /\
     (!x:real. continuous_real (\y:real. f (x,y)))
     ==> ?g:num->(real#real)->real.
           (!n:num. continuous_plane (g n)) /\
           tends_pointwise g f`;;
