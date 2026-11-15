(*
  Statement-only formalization of PutnamBench artifact putnam_1973_b2:
  for a unit complex number with rational real and imaginary parts, the
  modulus of z^(2n) - 1 is rational for every integer n. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open integerTheory ratTheory realTheory intrealTheory real_of_ratTheory
     complexTheory;

val putnam_1973_b2 =
  ``!z : complex.
      (?q1 q2 : rat.
         RE z = real_of_rat q1 /\
         IM z = real_of_rat q2) /\
      modu z = 1
      ==>
      let complex_int_pow =
        \n : int.
          if 0 <= n then z pow (Num n)
          else inv (z pow (Num (-n)))
      in
        !n : int.
          ?q : rat.
            modu (complex_int_pow (2 * n) - 1) = real_of_rat q``;
