(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/memb_free_Why3_ide_VCmemb_free_assert_rte_mem_access_4_goal11:
  a Contiki memb-free memory-access verification condition concluding that the
  structure's pointer field is readable under the stated memory, framing,
  integer-range, pointer-index, and scan-prefix assumptions. This file contains
  no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !t_3:(int#int)->(int#int).
   !t_1:(int#int)->int.
   !a_1 a:int#int.
   !t:int->int.
   !t_2:(int#int)->int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let cdiv =
       \(n:int) (d:int).
         if (&0:int) <= n
         then if (&0:int) <= d then n div d else --(n div --d)
         else if (&0:int) <= d then --(--n div d) else --n div --d in
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
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let is_uint16 =
       \z:int.
         (&0:int) <= z /\ z < (&65536:int) in
     let p_valid_memb =
       \(malloc:int->int)
        (mptr:(int#int)->(int#int))
        (mint:(int#int)->int)
        (m:int#int).
         let elem_size = mint (shift m (&0:int)) in
         let count = mint (shift m (&1:int)) in
         let total_size = count * elem_size in
         let used = mptr (shift m (&2:int)) in
         let memory = mptr (shift m (&3:int)) in
         let used_start = shift used (&0:int) in
         let memory_start = shift memory (&0:int) in
         (&0:int) < elem_size /\
         total_size <= (&2147483647:int) /\
         valid_rw malloc m (&4:int) /\
         valid_rw malloc used (&1:int) /\
         valid_rw malloc memory (&1:int) /\
         valid_rw malloc used_start count /\
         valid_rw malloc memory_start total_size /\
         separated used_start count memory_start total_size in
     let l__memb_ptr =
       \(mptr:(int#int)->(int#int))
        (mint:(int#int)->int)
        (m:int#int)
        (index:int).
         shift (mptr (shift m (&3:int)))
           (index * mint (shift m (&0:int))) in
     let l__memb_index =
       \(mptr:(int#int)->(int#int))
        (mint:(int#int)->int)
        (m:int#int)
        (ptr:int#int).
         cdiv
           (SND ptr - SND (mptr (shift m (&3:int))))
           (mint (shift m (&0:int))) in
     let x = l__memb_index t_3 t_1 a_1 a in
     let a_2 = shift a_1 (&1:int) in
     let x_1 = t_1 a_2 in
     let a_3 = shift a_1 (&3:int) in
     l__memb_ptr t_3 t_1 a_1 x = a
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> (&0:int) <= x
     ==> x < x_1
     ==> x <= x_1
     ==> framed t_3
     ==> linked t
     ==> sconst t_2
     ==> is_uint16 x_1
     ==> p_valid_memb t t_3 t_1 a_1
     ==> valid_rd t a_3 (&1:int)
     ==> valid_rd t a_2 (&1:int)
     ==> is_sint32 x
     ==> (!i:int.
            (&0:int) <= i
            ==> i < x
            ==> ~(shift (t_3 a_3)
                    (i * t_1 (shift a_1 (&0:int))) = a))
     ==> valid_rd t (shift a_1 (&2:int)) (&1:int)`;;
