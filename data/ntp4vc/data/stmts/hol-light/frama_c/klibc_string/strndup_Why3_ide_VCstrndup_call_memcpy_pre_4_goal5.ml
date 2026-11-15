(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_string/strndup_Why3_ide_VCstrndup_call_memcpy_pre_4_goal5:
  a strndup-to-memcpy call-precondition verification condition asserting
  writable validity of the source range for the selected string length,
  under the stated nonnull, index, memory-region, linking, constancy,
  unsigned-range, destination-validity, and null-character occurrence
  assumptions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !to_uint32:int->int.
   !i_1:int.
   !a a_1:int#int.
   !i:int.
   !t:int->int.
   !t_1:(int#int)->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let valid_rw =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST p /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let x = to_uint32 ((&1:int) + i_1) in
     let a_2 = shift a (&0:int) in
     (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> ~(((&0:int),(&0:int)) = a_1)
     ==> ~(x = (&0:int))
     ==> (&0:int) <= i
     ==> region (FST a) <= (&0:int)
     ==> linked t
     ==> sconst t_1
     ==> is_uint32 i
     ==> is_uint32 i_1
     ==> valid_rw t a_2 i
     ==> ((&0:int) < x
          ==> valid_rw t (shift a_1 (&0:int)) x)
     ==> ((!i_2:int.
            (&0:int) <= i_2
            ==> i_2 < i
            ==> ~(t_1 (shift a i_2) = (&0:int)))
          ==> i_1 = i)
     ==> ((?i_2:int.
            t_1 (shift a i_2) = (&0:int) /\
            (&0:int) <= i_2 /\
            i_2 < i)
          ==> i_1 <= i)
     ==> valid_rw t a_2 i_1`;;
