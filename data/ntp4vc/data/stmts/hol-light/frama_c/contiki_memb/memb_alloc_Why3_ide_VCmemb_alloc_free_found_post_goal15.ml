(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_free_found_post_goal15:
  a Contiki memb-allocation verification condition stating that a successful
  scan returns a free slot changed from zero to one, its corresponding block
  address, and agreement of the old and new usage maps at every other slot.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !a_1:int#int.
   !t_4:(int#int)->(int#int).
   !t_1:(int#int)->int.
   !i_2:int.
   !t_3:(int#int)->int.
   !i i_1:int.
   !t:int->int.
   !t_2:(int#int)->int.
   !a:int#int.
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
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
     let is_uint16 =
       \z:int.
         (&0:int) <= z /\ z < (&65536:int) in
     let update =
       \(f:(int#int)->int) (p:int#int) (v:int) (q:int#int).
         if q = p then v else f q in
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
     let a_2 = shift a_1 (&2:int) in
     let a_3 = t_4 a_2 in
     let a_4 = shift a_1 (&1:int) in
     let x = t_1 a_4 in
     let a_5 = shift a_1 (&0:int) in
     let x_1 = t_1 a_5 in
     let a_6 = shift a_3 i_2 in
     let a_7 = shift a_1 (&3:int) in
     let a_8 = t_4 a_7 in
     let x_2 = i_2 * x_1 in
     t_3 (shift a_3 i) = (&0:int)
     ==> (&0:int) <= i
     ==> (&0:int) <= i_1
     ==> i < x
     ==> i_1 <= x
     ==> region (FST a_1) <= (&0:int)
     ==> framed t_4
     ==> linked t
     ==> sconst t_3
     ==> is_sint32 i_1
     ==> is_sint32 i_2
     ==> is_uint16 x
     ==> is_uint16 x_1
     ==> p_valid_memb t t_4 t_1 a_1
     ==> valid_rd t a_4 (&1:int)
     ==> (if i_1 < x
          then i_2 = i_1 /\
               t_3 a_6 = (&0:int) /\
               update t_3 a_6 (&1:int) = t_2 /\
               shift a_8 x_2 = a /\
               --(&2147483648:int) <= x_2 /\
               x_2 <= (&2147483647:int) /\
               valid_rd t a_2 (&1:int) /\
               valid_rd t a_7 (&1:int) /\
               valid_rd t a_5 (&1:int) /\
               valid_rd t a_6 (&1:int) /\
               valid_rw t a_6 (&1:int)
          else t_3 = t_2 /\ ((&0:int),(&0:int)) = a)
     ==> (!i_3:int.
            (&0:int) <= i_3
            ==> i_3 < i_1
            ==> ~(t_3 (shift a_3 i_3) = (&0:int)))
     ==> (?i_3:int.
            let a_9 = shift a_3 i_3 in
            t_2 a_9 = (&1:int) /\
            t_3 a_9 = (&0:int) /\
            shift a_8 (i_3 * x_1) = a /\
            (&0:int) <= i_3 /\
            i_3 < x /\
            (!i_4:int.
               let a_10 = shift a_3 i_4 in
               ((&0:int) <= i_4 /\ i_4 < i_3 \/
                i_3 < i_4 /\ i_4 < x)
               ==> t_3 a_10 = t_2 a_10))`;;
