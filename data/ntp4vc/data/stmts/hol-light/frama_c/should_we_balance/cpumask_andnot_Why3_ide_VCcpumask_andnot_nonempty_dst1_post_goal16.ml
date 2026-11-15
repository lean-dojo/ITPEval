(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/should_we_balance/cpumask_andnot_Why3_ide_VCcpumask_andnot_nonempty_dst1_post_goal16:
  a cpumask-and-not verification condition asserting the destination-mask
  nonemptiness characterization at a bounded index, under the stated integer,
  memory-validity, framing, separation, and preceding-loop assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !to_uint32:int->int.
   !l_size:int.
   !l_idle_cpu:int->int.
   !l_cpu_smt_mask:int->(int#int).
   !t_3:(int#int)->(int#int).
   !a a_1 a_2:int#int.
   !t_1 t_2:(int#int)->int.
   !i i_1:int.
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
     let a_3 = t_3 (shift a (&0:int)) in
     let a_4 = shift a_3 (&0:int) in
     let a_5 = t_3 (shift a_1 (&0:int)) in
     let a_6 = shift a_5 (&0:int) in
     let a_7 = t_3 (shift a_2 (&0:int)) in
     let a_8 = shift a_7 (&0:int) in
     let a_9 = havoc t_1 t_2 a_8 l_size in
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
     ==> to_uint32 i = l_size
     ==> (&0:int) <= i
     ==> (&0:int) <= i_1
     ==> i_1 < l_size
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
     ==> valid_rd t a_4 l_size
     ==> valid_rd t a_6 l_size
     ==> valid_rw t a_8 l_size
     ==> (~(a_2 = a)
          ==> separated a_8 l_size a_4 l_size)
     ==> (~(a_2 = a_1)
          ==> separated a_8 l_size a_6 l_size)
     ==> (!i_2:int.
            (&0:int) <= i_2
            ==> i_2 < l_size
            ==> separated a_8 l_size
                  (shift (t_3 (shift (l_cpu_smt_mask i_2)
                                     (&0:int)))
                         (&0:int))
                  l_size)
     ==> (!i_2:int.
            let a_10 = shift a_7 i_2 in
            i <= i_2
            ==> i_2 < l_size
            ==> (~(a_9 a_10 = (&0:int)) <=>
                 ~(t_2 a_10 = (&0:int))))
     ==> (!i_2:int.
            (&0:int) <= i_2
            ==> i_2 < i
            ==> (t_2 (shift a_3 i_2) = (&0:int) /\
                 ~(t_2 (shift a_5 i_2) = (&0:int)) <=>
                 ~(a_9 (shift a_7 i_2) = (&0:int))))
     ==> (t_2 (shift a_3 i_1) = (&0:int) /\
          ~(t_2 (shift a_5 i_1) = (&0:int)) <=>
          ~(a_9 (shift a_7 i_1) = (&0:int)))`;;
