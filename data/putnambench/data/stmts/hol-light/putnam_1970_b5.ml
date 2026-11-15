(*
  Statement-only formalization of PutnamBench artifact putnam_1970_b5:
  continuity of a real function is equivalent to continuity of all its
  compositions with symmetric clipping maps. This file contains no proof.
*)

let statement =
  `let continuous =
     \(f:real->real).
       !x e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !y:real. abs (y - x) < d ==> abs (f y - f x) < e in
   let ramp =
     \n:num. \x:real.
       if x <= --(&n) then --(&n)
       else if --(&n) < x /\ x <= &n then x
       else &n in
   !f:real->real.
     continuous f <=>
     !n:num. continuous (ramp n o f)`;;
