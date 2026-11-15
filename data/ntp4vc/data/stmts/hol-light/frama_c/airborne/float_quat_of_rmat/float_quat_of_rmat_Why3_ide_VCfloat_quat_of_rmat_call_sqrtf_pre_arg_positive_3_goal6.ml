(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_call_sqrtf_pre_arg_positive_3_goal6:
  nonnegativity of the square-root argument in the branch selecting the
  middle diagonal entry of a special orthogonal 3-by-3 rotation matrix stored
  in memory. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !is_float32 finite32:real->bool.
   !a a_1:int#int.
   !t_1:(int#int)->real.
   !t:int->int.
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
     let separated =
       \(p:int#int) (n:int) (q:int#int) (m:int).
         n <= (&0:int) \/
         m <= (&0:int) \/
         ~(FST p = FST q) \/
         SND q + m <= SND p \/
         SND p + n <= SND q in
     let a_2 = shift a (&0:int) in
     let p0 = shift a_2 (&0:int) in
     let p1 = shift a_2 (&1:int) in
     let p2 = shift a_2 (&2:int) in
     let p3 = shift a_2 (&3:int) in
     let p4 = shift a_2 (&4:int) in
     let p5 = shift a_2 (&5:int) in
     let p6 = shift a_2 (&6:int) in
     let p7 = shift a_2 (&7:int) in
     let p8 = shift a_2 (&8:int) in
     let r = t_1 p8 in
     let r_1 = t_1 p4 in
     let r_2 = t_1 p0 in
     let r_3 = r_2 + r_1 + r in
     let finite_rmat =
       (
       finite32 (t_1 p0) /\
       finite32 (t_1 p1) /\
       finite32 (t_1 p2) /\
       finite32 (t_1 p3) /\
       finite32 (t_1 p4) /\
       finite32 (t_1 p5) /\
       finite32 (t_1 p6) /\
       finite32 (t_1 p7) /\
       finite32 (t_1 p8)) in
     let rotation_matrix =
       (
       t_1 p0 * t_1 p0 + t_1 p1 * t_1 p1 + t_1 p2 * t_1 p2 = &1 /\
       t_1 p0 * t_1 p3 + t_1 p1 * t_1 p4 + t_1 p2 * t_1 p5 = &0 /\
       t_1 p0 * t_1 p6 + t_1 p1 * t_1 p7 + t_1 p2 * t_1 p8 = &0 /\
       t_1 p3 * t_1 p0 + t_1 p4 * t_1 p1 + t_1 p5 * t_1 p2 = &0 /\
       t_1 p3 * t_1 p3 + t_1 p4 * t_1 p4 + t_1 p5 * t_1 p5 = &1 /\
       t_1 p3 * t_1 p6 + t_1 p4 * t_1 p7 + t_1 p5 * t_1 p8 = &0 /\
       t_1 p6 * t_1 p0 + t_1 p7 * t_1 p1 + t_1 p8 * t_1 p2 = &0 /\
       t_1 p6 * t_1 p3 + t_1 p7 * t_1 p4 + t_1 p8 * t_1 p5 = &0 /\
       t_1 p6 * t_1 p6 + t_1 p7 * t_1 p7 + t_1 p8 * t_1 p8 = &1) in
     let special_orthogonal =
       (
       t_1 p0 * t_1 p4 * t_1 p8 +
       t_1 p1 * t_1 p5 * t_1 p6 +
       t_1 p2 * t_1 p3 * t_1 p7 -
       t_1 p0 * t_1 p5 * t_1 p7 -
       t_1 p1 * t_1 p3 * t_1 p8 -
       t_1 p2 * t_1 p4 * t_1 p6 = &1) in
     (!x:real. is_float32 x) /\
     (!x:real. finite32 x)
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> r < r_1
     ==> r_3 <= &0
     ==> linked t
     ==> valid_rw t a_1 (&4:int)
     ==> finite_rmat /\ valid_rd t a (&9:int)
     ==> separated a (&9:int) a_1 (&4:int)
     ==> rotation_matrix
     ==> special_orthogonal
     ==> is_float32 r_2
     ==> is_float32 (t_1 p2)
     ==> is_float32 r_1
     ==> is_float32 (t_1 p6)
     ==> is_float32 r
     ==> is_float32 r_3
     ==> r_2 <= r_1 \/ r_2 <= r
     ==> &0 <= r_1 + --r_2 + --r + &1`;;
