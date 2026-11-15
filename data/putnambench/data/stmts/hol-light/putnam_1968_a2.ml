(*
  Statement-only formalization of PutnamBench artifact putnam_1968_a2:
  simultaneous nonzero rational approximation of two integer linear forms
  when their coefficient determinant is nonzero. This file contains no proof.
*)

let statement =
  `let is_rational = \x:real.
     ?p q:int.
       ~(q = (&0:int)) /\
       x = real_of_int p / real_of_int q in
   !a b c d e f:int.
     !epsilon:real.
       ~(a * d = b * c) /\
       &0 < epsilon
       ==> ?r s:real.
             is_rational r /\
             is_rational s /\
             &0 <
             abs (r * real_of_int a +
                  s * real_of_int b -
                  real_of_int e) /\
             abs (r * real_of_int a +
                  s * real_of_int b -
                  real_of_int e) < epsilon /\
             &0 <
             abs (r * real_of_int c +
                  s * real_of_int d -
                  real_of_int f) /\
             abs (r * real_of_int c +
                  s * real_of_int d -
                  real_of_int f) < epsilon`;;
