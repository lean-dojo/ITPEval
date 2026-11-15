(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/airborne/float_rmat_inv/float_rmat_inv_Why3_ide_VCfloat_rmat_inv_post_goal0:
  nine sequential memory updates copy a readable finite floating-point
  3-by-3 matrix into a writable destination in transposed layout.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !a a_1:int#int.
   !t_1:(int#int)->real.
   !t:int->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let update =
       \(f:(int#int)->real) (p:int#int) (x:real) (q:int#int).
         if q = p then x else f q in
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
     let finite32 = \x:real. T in
     let finite_floatrmat =
       \(mem:(int#int)->real) (rm:int#int).
         let b = shift rm (&0:int) in
         finite32 (mem (shift b (&0:int))) /\
         finite32 (mem (shift b (&1:int))) /\
         finite32 (mem (shift b (&2:int))) /\
         finite32 (mem (shift b (&3:int))) /\
         finite32 (mem (shift b (&4:int))) /\
         finite32 (mem (shift b (&5:int))) /\
         finite32 (mem (shift b (&6:int))) /\
         finite32 (mem (shift b (&7:int))) /\
         finite32 (mem (shift b (&8:int))) in
     let rvalid_floatrmat =
       \(malloc:int->int) (mem:(int#int)->real) (rm:int#int).
         finite_floatrmat mem rm /\
         valid_rd malloc rm (&9:int) in
     let matrix_of_memory =
       \(mem:(int#int)->real) (rm:int#int).
         let b = shift rm (&0:int) in
         (mem (shift b (&0:int)),
          (mem (shift b (&1:int)),
           (mem (shift b (&2:int)),
            (mem (shift b (&3:int)),
             (mem (shift b (&4:int)),
              (mem (shift b (&5:int)),
               (mem (shift b (&6:int)),
                (mem (shift b (&7:int)),
                 mem (shift b (&8:int)))))))))) in
     let transpose_of_memory =
       \(mem:(int#int)->real) (rm:int#int).
         let b = shift rm (&0:int) in
         (mem (shift b (&0:int)),
          (mem (shift b (&3:int)),
           (mem (shift b (&6:int)),
            (mem (shift b (&1:int)),
             (mem (shift b (&4:int)),
              (mem (shift b (&7:int)),
               (mem (shift b (&2:int)),
                (mem (shift b (&5:int)),
                 mem (shift b (&8:int)))))))))) in
     let a_2 = shift a (&0:int) in
     let a_3 = shift a_1 (&0:int) in
     let m =
       update t_1 (shift a_2 (&0:int))
         (t_1 (shift a_3 (&0:int))) in
     let m_1 =
       update m (shift a_2 (&1:int))
         (m (shift a_3 (&3:int))) in
     let m_2 =
       update m_1 (shift a_2 (&2:int))
         (m_1 (shift a_3 (&6:int))) in
     let m_3 =
       update m_2 (shift a_2 (&3:int))
         (m_2 (shift a_3 (&1:int))) in
     let m_4 =
       update m_3 (shift a_2 (&4:int))
         (m_3 (shift a_3 (&4:int))) in
     let m_5 =
       update m_4 (shift a_2 (&5:int))
         (m_4 (shift a_3 (&7:int))) in
     let m_6 =
       update m_5 (shift a_2 (&6:int))
         (m_5 (shift a_3 (&2:int))) in
     let m_7 =
       update m_6 (shift a_2 (&7:int))
         (m_6 (shift a_3 (&5:int))) in
     let m_8 =
       update m_7 (shift a_2 (&8:int))
         (m_7 (shift a_3 (&8:int))) in
     region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> linked t
     ==> valid_rw t a (&9:int)
     ==> rvalid_floatrmat t t_1 a_1
     ==> separated a (&9:int) a_1 (&9:int)
     ==> matrix_of_memory m_8 a = transpose_of_memory m_8 a_1`;;
