(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_rmat_integrate_fi/float_rmat_integrate_fi_Why3_ide_VCfloat_rmat_integrate_fi_call_float_rmat_comp_pre_2_goal0:
  read-validity of a nine-entry floating-point rotation matrix under the
  memory and floating-point preconditions for matrix composition.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !finite32 is_float32:real->bool.
   !a a_1:int#int.
   !t:int->int.
   !t_1:(int#int)->real.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let valid_rw =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST p /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let valid_rd =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> ~((&0:int) = FST p) /\
             (&0:int) <= SND p /\
             SND p + n <= malloc (FST p) in
     let finite_floatrates =
       \(mem:(int#int)->real) (r:int#int).
         finite32 (mem (shift r (&0:int))) /\
         finite32 (mem (shift r (&1:int))) /\
         finite32 (mem (shift r (&2:int))) in
     let rvalid_floatrates =
       \(malloc:int->int) (mem:(int#int)->real) (r:int#int).
         finite_floatrates mem r /\
         valid_rd malloc r (&3:int) in
     let finite_floatrmat =
       \(mem:(int#int)->real) (rm:int#int).
         let rmat_base = shift rm (&0:int) in
         finite32 (mem (shift rmat_base (&0:int))) /\
         finite32 (mem (shift rmat_base (&1:int))) /\
         finite32 (mem (shift rmat_base (&2:int))) /\
         finite32 (mem (shift rmat_base (&3:int))) /\
         finite32 (mem (shift rmat_base (&4:int))) /\
         finite32 (mem (shift rmat_base (&5:int))) /\
         finite32 (mem (shift rmat_base (&6:int))) /\
         finite32 (mem (shift rmat_base (&7:int))) /\
         finite32 (mem (shift rmat_base (&8:int))) in
     let rvalid_floatrmat =
       \(malloc:int->int) (mem:(int#int)->real) (rm:int#int).
         finite_floatrmat mem rm /\
         valid_rd malloc rm (&9:int) in
     (!x:real. finite32 x) /\
     (!x:real. is_float32 x)
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> linked t
     ==> valid_rw t a (&9:int)
     ==> rvalid_floatrates t t_1 a_1
     ==> is_float32 (t_1 (shift a_1 (&0:int)))
     ==> is_float32 (t_1 (shift a_1 (&1:int)))
     ==> is_float32 (t_1 (shift a_1 (&2:int)))
     ==> rvalid_floatrmat t t_1 a`;;
