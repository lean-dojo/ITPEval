(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/memb_init_Why3_ide_VCmemb_init_call_memset_pre_valid_s_goal9:
  a Contiki memb-initialization verification condition concluding that the
  pointer stored in the third structure field is valid or empty for the block
  count stored in the second field. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !a:int#int.
   !t_1:(int#int)->int.
   !t_3:(int#int)->(int#int).
   !t:int->int.
   !t_2:(int#int)->int.
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
     let p_empty_block =
       \(malloc:int->int) (s:int#int).
         malloc (FST s) = (&0:int) /\ SND s = (&0:int) in
     let p_valid_or_empty =
       \(malloc:int->int) (s:int#int) (n:int).
         valid_rw malloc (shift s (&0:int)) n /\
         (p_empty_block malloc s \/
          valid_rd malloc s (&1:int)) in
     let a_1 = shift a (&1:int) in
     let x = t_1 a_1 in
     let a_2 = shift a (&2:int) in
     region (FST a) <= (&0:int)
     ==> framed t_3
     ==> linked t
     ==> sconst t_2
     ==> is_uint16 x
     ==> is_uint16 (t_1 (shift a (&0:int)))
     ==> p_valid_memb t t_3 t_1 a
     ==> valid_rd t a_2 (&1:int)
     ==> valid_rd t a_1 (&1:int)
     ==> p_valid_or_empty t (t_3 a_2) x`;;
