(*
  Statement-only formalization of PutnamBench artifact putnam_1971_a1:
  nine lattice points in three-dimensional space contain two distinct points
  whose open line segment contains a lattice point. This file contains no proof.
*)

let statement =
  `!S:(int#int#int)->bool.
     S HAS_SIZE 9
     ==> ?x y z a b c d e f:int.
           (a,b,c) IN S /\
           (d,e,f) IN S /\
           ~((a,b,c) = (d,e,f)) /\
           ?t:real.
             &0 < t /\ t < &1 /\
             real_of_int x =
               t * real_of_int a + (&1 - t) * real_of_int d /\
             real_of_int y =
               t * real_of_int b + (&1 - t) * real_of_int e /\
             real_of_int z =
               t * real_of_int c + (&1 - t) * real_of_int f`;;
