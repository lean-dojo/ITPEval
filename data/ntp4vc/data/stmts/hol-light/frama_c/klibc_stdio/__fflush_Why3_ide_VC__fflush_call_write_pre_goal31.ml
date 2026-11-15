(*
  Statement-only formalization of NTP4VC corpus artifact
  frama_c/klibc_stdio/__fflush_Why3_ide_VC__fflush_call_write_pre_goal31:
  nonnegativity of the integer loaded at offset zero of a valid buffered I/O
  file object before the fflush write call, under the memory, bounds, and
  pointer-order preconditions. This file contains no proof.
*)

let statement =
  `!region:int->int.
   !linked:(int->int)->bool.
   !addr_le:(int#int)->(int#int)->bool.
   !addr_lt:(int#int)->(int#int)->bool.
   !t_2:(int#int)->(int#int).
   !a_1 a:int#int.
   !t_1:(int#int)->int.
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
     let is_sint32 =
       \z:int.
         --(&2147483648:int) <= z /\ z < (&2147483648:int) in
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
     let a_2 = t_2 (shift a_1 (&5:int)) in
     let x = FST a_2 in
     let x_1 = FST a in
     let x_2 = FST (t_2 (shift a_1 (&6:int))) in
     let x_3 = t_1 (shift a_1 (&9:int)) in
     let x_4 = t_1 (shift (shift a_1 (&0:int)) (&0:int)) in
     (!p q:int#int.
        FST p = FST q
        ==> (addr_le p q <=> SND p <= SND q))
     ==> (!p q:int#int.
           FST p = FST q
           ==> (addr_lt p q <=> SND p < SND q))
     ==> ~(i = (&0:int))
     ==> t_1 (shift a_1 (&7:int)) = (&0:int)
     ==> x = x_1
     ==> x_2 = x_1
     ==> x_2 = x
     ==> (&0:int) <= i
     ==> i_1 <= i
     ==> region (FST a_1) <= (&0:int)
     ==> --(&1:int) <= i_1
     ==> framed t_2
     ==> linked t
     ==> is_uint32 i
     ==> is_sint32 i_1
     ==> is_uint32 x_3
     ==> is_uint32 (t_1 (shift a_1 (&8:int)))
     ==> p_valid_io_file_pvt t t_2 t_1 a_1
     ==> addr_le a_2 a
     ==> valid_rw t (shift a (&0:int)) i
     ==> is_sint32 x_4
     ==> addr_le a (shift a_2 ((&32:int) + x_3))
     ==> (&0:int) <= x_4`;;
