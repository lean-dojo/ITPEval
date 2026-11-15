(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/verker/int_sqrt_Why3_ide_VCint_sqrt_loop_term_decrease_goal1:
  an integer square-root loop-termination verification condition stating that
  shifting a nonzero unsigned 64-bit integer right by two gives a strictly
  smaller integer under the stated range conditions. This file contains no
  proof.
*)

let statement =
  `!i_1 i:int.
     let is_uint64 =
       \z:int.
         (&0:int) <= z /\ z < (&18446744073709551616:int) in
     let x = (i_1 div (&2:int)) div (&2:int) in
     ~(i_1 = (&0:int))
     ==> (&2:int) <= i
     ==> is_uint64 i
     ==> is_uint64 i_1
     ==> is_uint64 x
     ==> x < i_1`;;
