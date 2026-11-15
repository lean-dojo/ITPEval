(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/contiki_memb/memb_free_Why3_ide_VCmemb_free_alloc_found_post_2_goal16:
  a Contiki memb-free verification condition stating that clearing an
  allocated slot increases the number of free slots by one, under the given
  memory, framing, integer-range, pointer-index, and scan-prefix assumptions.
  This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !a_1:int#int.
   !t_2:(int#int)->int.
   !t_5:(int#int)->(int#int).
   !i_1 i:int.
   !a:int#int.
   !t:int->int.
   !t_4:(int#int)->int.
   !t_1:int->int.
   !t_3:(int#int)->int.
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
     let update =
       \(f:(int#int)->int) (p:int#int) (v:int) (q:int#int).
         if q = p then v else f q in
     let l_occ_a =
       \(mchar:(int#int)->int) (e:int) (p:int#int)
        (from_index:int) (to_index:int).
         (&(CARD
              {j:int |
                 from_index <= j /\
                 j < to_index /\
                 mchar (shift p j) = e}):int) in
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
     let p__memb_has =
       \(mptr:(int#int)->(int#int))
        (mint:(int#int)->int)
        (m:int#int)
        (ptr:int#int).
         ?j:int.
           l__memb_ptr mptr mint m j = ptr /\
           (&0:int) <= j /\
           j < mint (shift m (&1:int)) in
     let p__memb_allocated =
       \(mptr:(int#int)->(int#int))
        (mchar:(int#int)->int)
        (mint:(int#int)->int)
        (m:int#int)
        (ptr:int#int).
         ~(mchar
             (shift (mptr (shift m (&2:int)))
               (l__memb_index mptr mint m ptr)) = (&0:int)) /\
         p__memb_has mptr mint m ptr in
     let l__memb_numfree =
       \(mptr:(int#int)->(int#int))
        (mchar:(int#int)->int)
        (mint:(int#int)->int)
        (m:int#int).
         l_occ_a mchar (&0:int) (mptr (shift m (&2:int)))
           (&0:int) (mint (shift m (&1:int))) in
     let a_2 = shift a_1 (&1:int) in
     let x = t_2 a_2 in
     let a_3 = shift a_1 (&3:int) in
     let a_4 = shift a_1 (&2:int) in
     let a_5 = shift (t_5 a_4) i_1 in
     l__memb_index t_5 t_2 a_1 (l__memb_ptr t_5 t_2 a_1 i) = i
     ==> (&0:int) <= i
     ==> i <= x
     ==> region (FST a) <= (&0:int)
     ==> region (FST a_1) <= (&0:int)
     ==> framed t_5
     ==> linked t
     ==> sconst t_4
     ==> is_sint32 i
     ==> is_sint32 i_1
     ==> is_uint16 x
     ==> p_valid_memb t t_5 t_2 a_1
     ==> p__memb_has t_5 t_2 a_1 a
     ==> valid_rd t a_3 (&1:int)
     ==> valid_rd t a_2 (&1:int)
     ==> p__memb_allocated t_5 t_4 t_2 a_1 a
     ==> (if i < x
          then i_1 = i /\
               t_1 = t /\
               l__memb_ptr t_5 t_2 a_1 i_1 = a /\
               update t_4 a_5 (&0:int) = t_3 /\
               valid_rd t_1 a_4 (&1:int) /\
               valid_rd t_1 a_5 (&1:int) /\
               valid_rw t_1 a_5 (&1:int)
          else t_4 = t_3)
     ==> (!i_2:int.
            (&0:int) <= i_2
            ==> i_2 < i
            ==> ~(shift (t_5 a_3)
                    (i_2 * t_2 (shift a_1 (&0:int))) = a))
     ==> (&1:int) + l__memb_numfree t_5 t_4 t_2 a_1 =
         l__memb_numfree t_5 t_3 t_2 a_1`;;
