(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_stdio/_fwrite_Why3_ide_VC_fwrite_call___fflush_pre_part1_goal15:
  an fwrite precondition verification condition preserving private buffered-I/O
  file validity after three integer-memory point updates, under the stated
  bounds, memory-validity, framing, and linking assumptions. This file contains
  no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !sconst:((int#int)->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !addr_lt:(int#int)->(int#int)->bool.
   !t_1:(int#int)->int.
   !a_5:int#int.
   !i_3:int.
   !a_2 a:int#int.
   !i_4:int.
   !a_4:int#int.
   !t_3:(int#int)->(int#int).
   !t:int->int.
   !t_2:(int#int)->int.
   !a_1 a_3:int#int.
   !i i_1 i_2:int.
     let shift =
       \(p:int#int) (k:int). (FST p,SND p + k) in
     let valid_rw =
       \(malloc:int->int) (p:int#int) (n:int).
         (&0:int) < n
         ==> (&0:int) < FST p /\
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
     let is_uint32 =
       \z:int.
         (&0:int) <= z /\ z < (&4294967296:int) in
     let update =
       \(f:(int#int)->int) (p:int#int) (v:int) (q:int#int).
         if q = p then v else f q in
     let p_valid_file =
       \(malloc:int->int)
        (mint:(int#int)->int)
        (f:int#int).
         (&0:int) <= mint (shift f (&0:int)) /\
         valid_rw malloc f (&3:int) in
     let p_valid_io_file_pvt_norec =
       \(malloc:int->int)
        (mptr:(int#int)->(int#int))
        (mint:(int#int)->int)
        (f:int#int).
         let x = mint (shift f (&9:int)) in
         let x_1 = mint (shift f (&7:int)) in
         let x_2 = mint (shift f (&8:int)) in
         let a = mptr (shift f (&5:int)) in
         let a_1 = mptr (shift f (&6:int)) in
         let a_2 = mptr (shift f (&4:int)) in
         let a_3 = mptr (shift f (&3:int)) in
         let a_4 = shift a (&0:int) in
         let x_3 = (&32:int) + x in
         x = (&16384:int) /\
         (&0:int) <= x_1 /\
         x_1 < x /\
         (&0:int) <= x_2 /\
         x_2 < x /\
         valid_rw malloc f (&11:int) /\
         addr_le a a_1 /\
         p_valid_file malloc mint (shift f (&0:int)) /\
         valid_rw malloc a_2 (&11:int) /\
         valid_rw malloc a_3 (&11:int) /\
         separated f (&11:int) a_2 (&11:int) /\
         separated f (&11:int) a_3 (&11:int) /\
         separated a_2 (&11:int) a_3 (&11:int) /\
         valid_rw malloc a_4 x_3 /\
         separated f (&11:int) a_4 x_3 /\
         separated a_2 (&11:int) a_4 x_3 /\
         separated a_3 (&11:int) a_4 x_3 /\
         addr_lt a_1 (shift a x_3) in
     let p_valid_io_file_pvt =
       \(malloc:int->int)
        (mptr:(int#int)->(int#int))
        (mint:(int#int)->int)
        (f:int#int).
         let x = mint (shift f (&9:int)) in
         let a = mptr (shift f (&6:int)) in
         let a_1 = mptr (shift f (&5:int)) in
         let a_2 = mptr (shift f (&3:int)) in
         let a_3 = mptr (shift f (&4:int)) in
         let x_1 = mint (shift f (&7:int)) in
         let x_2 = mint (shift f (&8:int)) in
         let a_4 = shift a_1 (&0:int) in
         let x_3 = (&32:int) + x in
         x = (&16384:int) /\
         FST a = FST a_1 /\
         mptr (shift a_2 (&4:int)) = f /\
         mptr (shift a_3 (&3:int)) = f /\
         (&0:int) <= x_1 /\
         x_1 < x /\
         (&0:int) <= x_2 /\
         x_2 < x /\
         valid_rw malloc f (&11:int) /\
         addr_le a_1 a /\
         p_valid_file malloc mint (shift f (&0:int)) /\
         separated f (&11:int) a_3 (&11:int) /\
         separated f (&11:int) a_2 (&11:int) /\
         separated a_3 (&11:int) a_2 (&11:int) /\
         p_valid_io_file_pvt_norec malloc mptr mint a_3 /\
         p_valid_io_file_pvt_norec malloc mptr mint a_2 /\
         valid_rw malloc a_4 x_3 /\
         separated f (&11:int) a_4 x_3 /\
         separated a_3 (&11:int) a_4 x_3 /\
         separated a_2 (&11:int) a_4 x_3 /\
         addr_lt a (shift a_1 x_3) in
     let x = t_1 (shift a_5 (&10:int)) in
     let data_pointer = t_3 (shift a_5 (&6:int)) in
     let buffer_pointer = t_3 (shift a_5 (&5:int)) in
     let previous_file = t_3 (shift a_5 (&4:int)) in
     let next_file = t_3 (shift a_5 (&3:int)) in
     let input_bytes = t_1 (shift a_5 (&7:int)) in
     let buffer_start = shift buffer_pointer (&0:int) in
     let public_file = shift a_5 (&0:int) in
     let updated_t_1 =
       update
         (update
           (update t_1 (shift a_5 (&8:int)) i)
           (shift public_file (&1:int))
           i_1)
         (shift public_file (&2:int))
         i_2 in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (!p q:int#int.
           FST p = FST q
           ==> (addr_lt p q <=> SND p < SND q))
     ==> ~(i_3 = (&0:int))
     ==> shift a_2 (&0:int) = shift a (&0:int)
     ==> ~(x = (&1:int))
     ==> ~(x = (&2:int))
     ==> t_1 (shift a_5 (&9:int)) = (&16384:int)
     ==> FST data_pointer = FST buffer_pointer
     ==> t_3 (shift previous_file (&3:int)) = a_5
     ==> t_3 (shift next_file (&4:int)) = a_5
     ==> (&0:int) <= i
     ==> (&0:int) <= i_3
     ==> (&0:int) <= i_4
     ==> (&0:int) <= input_bytes
     ==> region (FST a_2) <= (&0:int)
     ==> region (FST a_4) <= (&0:int)
     ==> i <= (&16383:int)
     ==> input_bytes <= (&16383:int)
     ==> framed t_3
     ==> linked t
     ==> sconst t_2
     ==> is_uint32 i
     ==> is_uint32 i_3
     ==> is_uint32 i_4
     ==> valid_rw t a_5 (&11:int)
     ==> is_uint32 x
     ==> is_uint32 input_bytes
     ==> p_valid_io_file_pvt t t_3 t_1 a_1
     ==> p_valid_io_file_pvt t t_3 t_1 a_3
     ==> p_valid_io_file_pvt t t_3 t_1 a_5
     ==> addr_le buffer_pointer data_pointer
     ==> valid_rw t (shift a_4 (&0:int)) i_3
     ==> separated a_5 (&11:int) next_file (&11:int)
     ==> separated a_5 (&11:int) previous_file (&11:int)
     ==> separated next_file (&11:int) previous_file (&11:int)
     ==> addr_lt
           data_pointer
           (shift buffer_pointer (&16416:int))
     ==> valid_rw t buffer_start (&16416:int)
     ==> p_valid_file t updated_t_1 public_file
     ==> separated a_5 (&11:int) buffer_start (&16416:int)
     ==> separated next_file (&11:int) buffer_start (&16416:int)
     ==> separated previous_file (&11:int) buffer_start (&16416:int)
     ==> p_valid_io_file_pvt_norec
           t t_3 updated_t_1 next_file
     ==> p_valid_io_file_pvt_norec
           t t_3 updated_t_1 previous_file
     ==> p_valid_io_file_pvt
           t
           t_3
           updated_t_1
           a_5`;;
