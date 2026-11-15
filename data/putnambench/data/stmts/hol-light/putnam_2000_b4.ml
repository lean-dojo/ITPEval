(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_b4:
  a continuous real function satisfying f(2x^2 - 1) = 2x f(x) for every real
  x vanishes throughout the interval [-1,1]. This file contains no proof.
*)

let statement =
  `let continuous =
     \(f:real->real).
       !x e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !y:real.
                 abs (y - x) < d ==> abs (f y - f x) < e in
   !f:real->real.
     continuous f /\
     (!x:real. f (&2 * x pow 2 - &1) = &2 * x * f x)
     ==> !x:real.
           -- &1 <= x /\ x <= &1
           ==> f x = &0`;;
