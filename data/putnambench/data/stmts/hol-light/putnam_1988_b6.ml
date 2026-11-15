(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_b6:
  infinitely many ordered integer pairs preserve triangular-number membership
  under their affine map for every positive integer input. This file contains
  no proof.
*)

let statement =
  `let triangular =
     \t:int.
       ?n:int.
         (&0:int) <= n /\
         t = (n * (n + &1)) div &2 in
   INFINITE
     {(a,b):int#int |
        !t:int.
          (&0:int) < t
          ==> (triangular (a * t + b) <=> triangular t)}`;;
