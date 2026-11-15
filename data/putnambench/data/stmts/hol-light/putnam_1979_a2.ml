(*
  Statement-only formalization of PutnamBench artifact putnam_1979_a2:
  the real constants k for which a continuous real function f satisfies
  f(f(x)) = k*x^9 for every real x. This file contains no proof.
*)

let statement =
  `let continuous =
     \(f:real->real).
       !x e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !y:real. abs (y - x) < d ==> abs (f y - f x) < e in
   !k:real.
     ((?f:real->real.
         continuous f /\
         (!x:real. f (f x) = k * x pow 9)) <=>
      &0 <= k)`;;
