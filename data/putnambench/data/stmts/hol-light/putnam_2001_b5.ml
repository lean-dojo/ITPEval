(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_b5:
  a continuous real function whose second iterate is a fixed real linear
  combination of the function and its input must itself be linear through the
  origin. This file contains no proof.
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
   !a b:real.
   !g:real->real.
     &0 < a /\ a < &1 / &2 /\
     &0 < b /\ b < &1 / &2 /\
     continuous g /\
     (!x:real. g (g x) = a * g x + b * x)
     ==> ?c:real. !x:real. g x = c * x`;;
