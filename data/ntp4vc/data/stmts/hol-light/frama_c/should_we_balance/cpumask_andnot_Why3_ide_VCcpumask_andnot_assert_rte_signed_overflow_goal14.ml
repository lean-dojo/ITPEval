(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/cpumask_andnot_Why3_ide_VCcpumask_andnot_assert_rte_signed_overflow_goal14:
  a cpumask-and-not signed-overflow verification condition concluding that
  the loop index is at most 2147483646, under the stated integer-range,
  memory-validity, framing, separation, and mask-update assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !l_size:int.
   !l_idle_cpu:int->int.
   !l_cpu_smt_mask:int->(int#int).
   !a_1 a_2 a:int#int.
   !t_3:(int#int)->(int#int).
   !i:int.
   !t_1 t_2:(int#int)->int.
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
     let framed =
       \(mptr:(int#int)->(int#int)).
         !p:int#int. region (FST (mptr p)) <= (&0:int) in
     let is_uint8 =
       \z:int.
         (&0:int) <= z /\ z < (&256:int) in
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let havoc =
       \(m0:(int#int)->int)
        (m1:(int#int)->int)
        (p:int#int) (n:int) (q:int#int).
         if separated q (&1:int) p n then m1 q else m0 q in
     let a_3 = shift a_1 (&0:int) in
     let a_4 = shift a_2 (&0:int) in
     let a_5 = shift a (&0:int) in
     let a_6 = t_3 a_5 in
     let a_7 = shift a_6 (&0:int) in
     let a_8 = t_3 a_3 in
     let a_9 = shift a_8 (&0:int) in
     let a_10 = shift a_8 i in
     let a_11 = t_3 a_4 in
     let a_12 = shift a_11 (&0:int) in
     let a_13 = havoc t_1 t_2 a_12 l_size in
     let a_14 = shift a_6 i in
     let a_15 = a_13 a_14 in
     let a_16 = a_13 a_10 in
     ((&0:int) < l_size /\ l_size <= (&2147483647:int))
     ==> (!cpu:int. is_uint8 (l_idle_cpu cpu))
     ==> (!i_1:int.
            !mint:(int#int)->int.
            !mptr:(int#int)->(int#int).
              (&0:int) <= i_1
              ==> i_1 < l_size
              ==> ~(mint
                      (shift
                        (mptr
                          (shift (l_cpu_smt_mask i_1) (&0:int)))
                        i_1) =
                    (&0:int)))
     ==> (!mint:(int#int)->int.
            !mptr:(int#int)->(int#int).
            !j i_1:int.
              ~(mint
                  (shift
                    (mptr (shift (l_cpu_smt_mask j) (&0:int)))
                    i_1) =
                (&0:int))
              ==> (&0:int) <= i_1
              ==> i_1 < l_size
              ==> (&0:int) <= j
              ==> j < l_size
              ==> ~(mint
                      (shift
                        (mptr
                          (shift (l_cpu_smt_mask i_1) (&0:int)))
                        j) =
                    (&0:int)))
     ==> (!mptr:(int#int)->(int#int).
            !i_1:int.
            !mint:(int#int)->int.
            !j k:int.
              ~(mint
                  (shift
                    (mptr
                      (shift (l_cpu_smt_mask i_1) (&0:int)))
                    j) =
                (&0:int))
              ==> ~(mint
                      (shift
                        (mptr
                          (shift (l_cpu_smt_mask j) (&0:int)))
                        k) =
                    (&0:int))
              ==> (&0:int) <= i_1
              ==> i_1 < l_size
              ==> (&0:int) <= j
              ==> j < l_size
              ==> (&0:int) <= k
              ==> k < l_size
              ==> ~(mint
                      (shift
                        (mptr
                          (shift (l_cpu_smt_mask i_1) (&0:int)))
                        k) =
                    (&0:int)))
     ==> (!z:int. is_uint32 (to_uint32 z))
     ==> (!z:int. is_uint32 z ==> to_uint32 z = z)
     ==> ~(((&0:int),(&0:int)) = a_2)
     ==> ~(to_uint32 i = l_size)
     ==> (&0:int) <= i
     ==> i <= l_size
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> region (FST a_2) <= (&0:int)
     ==> framed t_3
     ==> linked t
     ==> is_sint32 i
     ==> valid_rd t a (&1:int)
     ==> valid_rd t a_1 (&1:int)
     ==> valid_rd t a_2 (&1:int)
     ==> valid_rd t a_3 (&1:int)
     ==> valid_rd t a_4 (&1:int)
     ==> valid_rd t a_7 l_size
     ==> valid_rd t a_9 l_size
     ==> valid_rd t a_10 (&1:int)
     ==> valid_rw t a_12 l_size
     ==> valid_rw t (shift a_11 i) (&1:int)
     ==> is_uint8 a_15
     ==> is_uint8 a_16
     ==> (~(a_2 = a)
          ==> separated a_12 l_size a_7 l_size)
     ==> (~(a_2 = a_1)
          ==> separated a_12 l_size a_9 l_size)
     ==> (a_16 = (&0:int) \/ a_16 = (&1:int))
     ==> (a_16 = (&0:int) \/
          valid_rd t a_5 (&1:int) /\
          valid_rd t a_14 (&1:int) /\
          (a_15 = (&0:int) \/ a_15 = (&1:int)))
     ==> (!i_1:int.
            (&0:int) <= i_1
            ==> i_1 < l_size
            ==> separated a_12 l_size
                  (shift (t_3 (shift (l_cpu_smt_mask i_1)
                                     (&0:int)))
                         (&0:int))
                  l_size)
     ==> (!i_1:int.
            let a_17 = shift a_11 i_1 in
            i <= i_1
            ==> i_1 < l_size
            ==> (~(a_13 a_17 = (&0:int)) <=>
                 ~(t_2 a_17 = (&0:int))))
     ==> (!i_1:int.
            (&0:int) <= i_1
            ==> i_1 < i
            ==> (t_2 (shift a_6 i_1) = (&0:int) /\
                 ~(t_2 (shift a_8 i_1) = (&0:int)) <=>
                 ~(a_13 (shift a_11 i_1) = (&0:int))))
     ==> i <= (&2147483646:int)`;;
