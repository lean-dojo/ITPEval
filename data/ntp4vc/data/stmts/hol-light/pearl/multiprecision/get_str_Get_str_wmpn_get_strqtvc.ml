(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/get_str_Get_str_wmpn_get_strqtvc: the call-site
  verification condition for dispatching conversion of a positive
  multiprecision integer to a digit string through the power-of-two or
  general-base routine over total integer-indexed memory maps with explicit
  allocation lengths, preserving value, range, leading-digit, and pointer
  frame contracts. This file contains no proof.
*)

let gmain_output = open_out "/dev/null";;
Format.pp_set_formatter_out_channel Format.std_formatter gmain_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

new_type_abbrev
  ("gmain_lptr",`:(int->int64)#(num#(int#(int#(int#(bool#Z)))))`);;
new_type_abbrev
  ("gmain_bptr",`:(int->byte)#(num#(int#(int#(int#(bool#Z)))))`);;
new_type_abbrev ("gmain_info",`:int#(int32#int64)`);;

let gmain_radix = new_definition
  `gmain_radix = (&18446744073709551616:int)`;;

let gmain_i32 = new_definition
  `gmain_i32 (x:int32) = ival x`;;

let gmain_u32 = new_definition
  `gmain_u32 (x:int32) = (&(val x):int)`;;

let gmain_u64 = new_definition
  `gmain_u64 (x:int64) = (&(val x):int)`;;

let gmain_u8 = new_definition
  `gmain_u8 (x:byte) = (&(val x):int)`;;

let gmain_i32_bounds = new_definition
  `gmain_i32_bounds (x:int) <=>
     --(&2147483648:int) <= x /\ x <= (&2147483647:int)`;;

let gmain_ipow = new_definition
  `gmain_ipow (base:int) (exponent:int) =
     base pow (if exponent < (&0:int) then 0 else num_of_int exponent)`;;

let gmain_ldata = new_definition
  `gmain_ldata (p:gmain_lptr) = FST p`;;

let gmain_bdata = new_definition
  `gmain_bdata (p:gmain_bptr) = FST p`;;

let gmain_llen = new_definition
  `gmain_llen (p:gmain_lptr) = FST (SND p)`;;

let gmain_blen = new_definition
  `gmain_blen (p:gmain_bptr) = FST (SND p)`;;

let gmain_loff = new_definition
  `gmain_loff (p:gmain_lptr) = FST (SND (SND p))`;;

let gmain_boff = new_definition
  `gmain_boff (p:gmain_bptr) = FST (SND (SND p))`;;

let gmain_lmin = new_definition
  `gmain_lmin (p:gmain_lptr) = FST (SND (SND (SND p)))`;;

let gmain_bmin = new_definition
  `gmain_bmin (p:gmain_bptr) = FST (SND (SND (SND p)))`;;

let gmain_lmax = new_definition
  `gmain_lmax (p:gmain_lptr) = FST (SND (SND (SND (SND p))))`;;

let gmain_bmax = new_definition
  `gmain_bmax (p:gmain_bptr) = FST (SND (SND (SND (SND p))))`;;

let gmain_lwrite = new_definition
  `gmain_lwrite (p:gmain_lptr) =
     FST (SND (SND (SND (SND (SND p)))))`;;

let gmain_bwrite = new_definition
  `gmain_bwrite (p:gmain_bptr) =
     FST (SND (SND (SND (SND (SND p)))))`;;

let gmain_lzone = new_definition
  `gmain_lzone (p:gmain_lptr) =
     SND (SND (SND (SND (SND (SND p)))))`;;

let gmain_bzone = new_definition
  `gmain_bzone (p:gmain_bptr) =
     SND (SND (SND (SND (SND (SND p)))))`;;

let gmain_lpelts = new_definition
  `gmain_lpelts p (i:int) = gmain_ldata p i`;;

let gmain_bpelts = new_definition
  `gmain_bpelts p (i:int) = gmain_bdata p i`;;

let gmain_lvalid = new_definition
  `gmain_lvalid p (size:int) <=>
     gmain_i32_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= gmain_lmin p /\
     gmain_lmin p <= gmain_loff p /\
     gmain_loff p + size <= gmain_lmax p /\
     gmain_lmax p <= (&(gmain_llen p):int)`;;

let gmain_bvalid = new_definition
  `gmain_bvalid p (size:int) <=>
     gmain_i32_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= gmain_bmin p /\
     gmain_bmin p <= gmain_boff p /\
     gmain_boff p + size <= gmain_bmax p /\
     gmain_bmax p <= (&(gmain_blen p):int)`;;

let gmain_same_bframe = new_definition
  `gmain_same_bframe newer older <=>
     gmain_blen newer = gmain_blen older /\
     gmain_boff newer = gmain_boff older /\
     gmain_bmin newer = gmain_bmin older /\
     gmain_bmax newer = gmain_bmax older /\
     gmain_bwrite newer = gmain_bwrite older /\
     gmain_bzone newer = gmain_bzone older`;;

let gmain_bframe = new_definition
  `gmain_bframe newer older (bound:int) <=>
     !j:int.
       j < gmain_boff newer \/ gmain_boff newer + bound <= j
       ==> gmain_bpelts newer j = gmain_bpelts older j`;;

let gmain_value = new_definition
  `gmain_value p (count:int) =
     if count <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int count - 1)
         (\k. gmain_radix pow k *
              gmain_u64 (gmain_lpelts p (gmain_loff p + &k)))`;;

let gmain_svalue_sub = new_definition
  `gmain_svalue_sub (base:int) (m:int->byte)
                    (lower:int) (upper:int) =
     let count = upper - lower in
     if count <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int count - 1)
         (\k. base pow (num_of_int count - 1 - k) *
              gmain_u8 (m (lower + &k)))`;;

let gmain_svalue = new_definition
  `gmain_svalue (base:int) p (count:int) =
     gmain_svalue_sub base (gmain_bpelts p)
       (gmain_boff p) (gmain_boff p + count)`;;

let gmain_in_base = new_definition
  `gmain_in_base (base:int) (m:int->byte)
                 (lower:int) (upper:int) <=>
     !k:int.
       lower <= k /\ k < upper
       ==> (&0:int) <= gmain_u8 (m k) /\ gmain_u8 (m k) < base`;;

let gmain_info_b = new_definition
  `gmain_info_b (info:gmain_info) = FST info`;;

let gmain_info_exp = new_definition
  `gmain_info_exp (info:gmain_info) = FST (SND info)`;;

let gmain_info_bb = new_definition
  `gmain_info_bb (info:gmain_info) = SND (SND info)`;;

let gmain_info_ok = new_definition
  `gmain_info_ok info <=>
     (&2:int) <= gmain_info_b info /\
     gmain_info_b info <= (&256:int) /\
     gmain_u64 (gmain_info_bb info) < gmain_radix /\
     gmain_radix <=
       gmain_u64 (gmain_info_bb info) * gmain_info_b info /\
     (&7:int) <= gmain_u32 (gmain_info_exp info) /\
     gmain_u32 (gmain_info_exp info) <= (&63:int) /\
     gmain_u64 (gmain_info_bb info) =
       gmain_ipow (gmain_info_b info)
         (gmain_u32 (gmain_info_exp info))`;;

let gmain_final_post = new_definition
  `gmain_final_post base up un sp1 size result <=>
     gmain_in_base (gmain_i32 base) (gmain_bpelts sp1)
       (gmain_boff sp1) (gmain_boff sp1 + gmain_u32 result) /\
     gmain_svalue (gmain_i32 base) sp1 (gmain_u32 result) =
       gmain_value up (gmain_i32 un) /\
     ((&0:int) < gmain_u32 result /\
      gmain_u32 result < gmain_i32 size) /\
     (&0:int) <
       gmain_u8 (gmain_bpelts sp1 (gmain_boff sp1))`;;

let gmain_bits_result_pre = new_definition
  `gmain_bits_result_pre up un original_sp bits o2 sp1 result <=>
     let allocation =
       (gmain_i32 o2 + gmain_u32 bits - (&1:int)) div gmain_u32 bits in
     gmain_in_base (gmain_ipow (&2:int) (gmain_u32 bits))
       (gmain_bpelts sp1) (gmain_boff sp1)
       (gmain_boff sp1 + gmain_u32 result) /\
     gmain_svalue (gmain_ipow (&2:int) (gmain_u32 bits))
       sp1 (gmain_u32 result) =
       gmain_value up (gmain_i32 un) /\
     ((&0:int) < gmain_u32 result /\
      gmain_u32 result <= allocation) /\
     (&0:int) <
       gmain_u8 (gmain_bpelts sp1 (gmain_boff sp1)) /\
     gmain_bframe sp1 original_sp allocation`;;

let gmain_bits_call = new_definition
  `gmain_bits_call base up un original_sp size bits o2 <=>
     let allocation =
       (gmain_i32 o2 + gmain_u32 bits - (&1:int)) div gmain_u32 bits in
     (&1:int) <= gmain_i32 un /\
     gmain_lvalid up (gmain_i32 un) /\
     ((&1:int) <= gmain_u32 bits /\
      gmain_u32 bits <= (&8:int)) /\
     gmain_bvalid original_sp allocation /\
     (&0:int) <= gmain_i32 o2 /\
     gmain_value up (gmain_i32 un) <
       gmain_ipow (&2:int) (gmain_i32 o2) /\
     (&0:int) <
       gmain_u64
         (gmain_lpelts up
           (gmain_loff up + gmain_i32 un - (&1:int))) /\
     (&64:int) * gmain_i32 un + (&7:int) <= (&2147483647:int) /\
     gmain_bwrite original_sp = T /\
     (!sp1:gmain_bptr.
        gmain_same_bframe sp1 original_sp
        ==>
        !result:int32.
          gmain_bits_result_pre
            up un original_sp bits o2 sp1 result
          ==>
          gmain_final_post base up un sp1 size result)`;;

let gmain_other_result_pre = new_definition
  `gmain_other_result_pre base up un original_sp size sp1 result <=>
     ((&0:int) <= gmain_u32 result /\
      gmain_u32 result < gmain_i32 size) /\
     gmain_svalue (gmain_i32 base) sp1 (gmain_u32 result) =
       gmain_value up (gmain_i32 un) /\
     gmain_in_base (gmain_i32 base) (gmain_bpelts sp1)
       (gmain_boff sp1) (gmain_boff sp1 + gmain_u32 result) /\
     (&0:int) <
       gmain_u8 (gmain_bpelts sp1 (gmain_boff sp1)) /\
     gmain_bframe sp1 original_sp (gmain_i32 size)`;;

let gmain_other_call = new_definition
  `gmain_other_call base up un original_sp size info <=>
     gmain_lvalid up (gmain_i32 un) /\
     (&1:int) <= gmain_i32 un /\
     gmain_info_b info = gmain_i32 base /\
     gmain_lwrite up = T /\
     gmain_bwrite original_sp = T /\
     (&0:int) <
       gmain_u64
         (gmain_lpelts up
           (gmain_loff up + gmain_i32 un - (&1:int))) /\
     (&0:int) < gmain_i32 size /\
     gmain_bvalid original_sp (gmain_i32 size) /\
     gmain_value up (gmain_i32 un) <
       gmain_ipow (gmain_i32 base) (gmain_i32 size - (&1:int)) /\
     (!sp1:gmain_bptr.
        gmain_same_bframe sp1 original_sp
        ==>
        !result:int32.
          gmain_other_result_pre
            base up un original_sp size sp1 result
          ==>
          gmain_final_post base up un sp1 size result)`;;

let gmain_bits_contract = new_definition
  `gmain_bits_contract o1 bits <=>
     ((&0:int) <= gmain_u32 bits /\
      gmain_u32 bits <= (&8:int)) /\
     (~(gmain_u32 bits = (&0:int))
      ==> gmain_ipow (&2:int) (gmain_u32 bits) = gmain_u64 o1) /\
     (gmain_u32 bits = (&0:int)
      ==> !n:int.
            (&0:int) <= n
            ==> ~(gmain_ipow (&2:int) n = gmain_u64 o1))`;;

let statement =
  `!size:int32. !un:int32. !sp:gmain_bptr. !up:gmain_lptr.
   !base:int32.
     (&0:int) < gmain_i32 size /\
     (&0:int) < gmain_i32 un /\
     gmain_bvalid sp (gmain_i32 size) /\
     gmain_lvalid up (gmain_i32 un) /\
     gmain_bwrite sp = T /\
     gmain_lwrite up = T /\
     gmain_ipow gmain_radix (gmain_i32 un) <=
       gmain_ipow (gmain_i32 base) (gmain_i32 size - (&1:int)) /\
     (&0:int) <
       gmain_u64
         (gmain_lpelts up
           (gmain_loff up + gmain_i32 un - (&1:int))) /\
     (&2:int) <= gmain_i32 base /\
     gmain_i32 base <= (&256:int) /\
     (&64:int) * gmain_i32 un + (&7:int) <= (&2147483647:int)
     ==>
     (&0:int) <= gmain_i32 base /\
     (!o1:int64.
        gmain_u64 o1 = gmain_i32 base
        ==>
        ((&2:int) <= gmain_u64 o1 /\
         gmain_u64 o1 <= (&256:int)) /\
        (!bits:int32.
           gmain_bits_contract o1 bits
           ==>
           (gmain_u32 bits = (&0:int)
            ==> bits = (word 0:int32))
           ==>
           if ~(bits = (word 0:int32)) then
             gmain_i32_bounds ((&64:int) * gmain_i32 un) /\
             (!o2:int32.
                gmain_i32 o2 = (&64:int) * gmain_i32 un
                ==>
                gmain_bits_call base up un sp size bits o2)
           else
             (&0:int) <= gmain_i32 base /\
             (!o2:int64.
                gmain_u64 o2 = gmain_i32 base
                ==>
                ((&2:int) <= gmain_u64 o2 /\
                 gmain_u64 o2 <= (&256:int)) /\
                (!info:gmain_info.
                   gmain_info_ok info
                   ==>
                   gmain_info_b info = gmain_u64 o2
                   ==>
                   gmain_other_call
                     base up un sp size info))))`;;

Format.pp_print_flush Format.std_formatter ();;
Format.pp_set_formatter_out_channel Format.std_formatter stdout;;
close_out gmain_output;;
