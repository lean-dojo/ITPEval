(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/get_str_Get_str_wmpn_get_str_bitsqtvc: the verification
  condition for converting a positive multiprecision integer to base-2^bits
  bytes while maintaining the digit-value, pointer-frame, and loop invariants.
  This file contains no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

new_type_abbrev
  ("gstr_lptr",`:(int64 list)#(int#(int#(int#(bool#Z))))`);;
new_type_abbrev
  ("gstr_bptr",`:(byte list)#(int#(int#(int#(bool#Z))))`);;

let gstr_radix = new_definition
  `gstr_radix = (&18446744073709551616:int)`;;

let gstr_u64 = new_definition
  `gstr_u64 (x:int64) = (&(val x):int)`;;

let gstr_u32 = new_definition
  `gstr_u32 (x:int32) = (&(val x):int)`;;

let gstr_u8 = new_definition
  `gstr_u8 (x:byte) = (&(val x):int)`;;

let gstr_int32_in_bounds = new_definition
  `gstr_int32_in_bounds (x:int) <=>
     --(&2147483648:int) <= x /\ x <= (&2147483647:int)`;;

let gstr_uint64_in_bounds = new_definition
  `gstr_uint64_in_bounds (x:int) <=>
     (&0:int) <= x /\ x <= (&18446744073709551615:int)`;;

let gstr_ipow = new_definition
  `gstr_ipow (base:int) (exponent:int) =
     base pow (if exponent < (&0:int) then 0 else num_of_int exponent)`;;

let gstr_cdiv = new_definition
  `gstr_cdiv (n:int) (d:int) =
     if (&0:int) <= n
     then if (&0:int) <= d then n div d else --(n div --d)
     else if (&0:int) <= d then --(--n div d) else --n div --d`;;

let gstr_cmod = new_definition
  `gstr_cmod (n:int) (d:int) = n - d * gstr_cdiv n d`;;

let gstr_ldata = new_definition `gstr_ldata (p:gstr_lptr) = FST p`;;
let gstr_bdata = new_definition `gstr_bdata (p:gstr_bptr) = FST p`;;
let gstr_loffset = new_definition `gstr_loffset (p:gstr_lptr) = FST (SND p)`;;
let gstr_boffset = new_definition `gstr_boffset (p:gstr_bptr) = FST (SND p)`;;
let gstr_lminimum = new_definition
  `gstr_lminimum (p:gstr_lptr) = FST (SND (SND p))`;;
let gstr_bminimum = new_definition
  `gstr_bminimum (p:gstr_bptr) = FST (SND (SND p))`;;
let gstr_lmaximum = new_definition
  `gstr_lmaximum (p:gstr_lptr) = FST (SND (SND (SND p)))`;;
let gstr_bmaximum = new_definition
  `gstr_bmaximum (p:gstr_bptr) = FST (SND (SND (SND p)))`;;
let gstr_lwritable = new_definition
  `gstr_lwritable (p:gstr_lptr) = FST (SND (SND (SND (SND p))))`;;
let gstr_bwritable = new_definition
  `gstr_bwritable (p:gstr_bptr) = FST (SND (SND (SND (SND p))))`;;
let gstr_lzone = new_definition
  `gstr_lzone (p:gstr_lptr) = SND (SND (SND (SND (SND p))))`;;
let gstr_bzone = new_definition
  `gstr_bzone (p:gstr_bptr) = SND (SND (SND (SND (SND p))))`;;

let gstr_lpelts = new_definition
  `gstr_lpelts p (i:int) =
     let k = if i < (&0:int) then 0 else num_of_int i in
     if k < LENGTH (gstr_ldata p) then EL k (gstr_ldata p)
     else (word 0:int64)`;;

let gstr_bpelts = new_definition
  `gstr_bpelts p (i:int) =
     let k = if i < (&0:int) then 0 else num_of_int i in
     if k < LENGTH (gstr_bdata p) then EL k (gstr_bdata p)
     else (word 0:byte)`;;

let gstr_lvalid = new_definition
  `gstr_lvalid p (size:int) <=>
     gstr_int32_in_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= gstr_lminimum p /\
     gstr_lminimum p <= gstr_loffset p /\
     gstr_loffset p + size <= gstr_lmaximum p /\
     gstr_lmaximum p <= (&(LENGTH (gstr_ldata p)):int)`;;

let gstr_bvalid = new_definition
  `gstr_bvalid p (size:int) <=>
     gstr_int32_in_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= gstr_bminimum p /\
     gstr_bminimum p <= gstr_boffset p /\
     gstr_boffset p + size <= gstr_bmaximum p /\
     gstr_bmaximum p <= (&(LENGTH (gstr_bdata p)):int)`;;

let gstr_laccess = new_definition
  `gstr_laccess p (index:int) <=>
     gstr_lminimum p <= gstr_loffset p + index /\
     gstr_loffset p + index < gstr_lmaximum p`;;

let gstr_baccess = new_definition
  `gstr_baccess p (index:int) <=>
     gstr_bminimum p <= gstr_boffset p + index /\
     gstr_boffset p + index < gstr_bmaximum p`;;

let gstr_same_bframe = new_definition
  `gstr_same_bframe newer older <=>
     LENGTH (gstr_bdata newer) = LENGTH (gstr_bdata older) /\
     gstr_boffset newer = gstr_boffset older /\
     gstr_bminimum newer = gstr_bminimum older /\
     gstr_bmaximum newer = gstr_bmaximum older /\
     gstr_bwritable newer = gstr_bwritable older /\
     gstr_bzone newer = gstr_bzone older`;;

let gstr_update = new_definition
  `gstr_update (f:int->A) (index:int) (value:A) =
     \query. if query = index then value else f query`;;

let gstr_value = new_definition
  `gstr_value p (count:int) =
     if count <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int count - 1)
         (\k. gstr_radix pow k *
              gstr_u64 (gstr_lpelts p (gstr_loffset p + &k)))`;;

let gstr_svalue_sub = new_definition
  `gstr_svalue_sub (base:int) (m:int->byte) (lower:int) (upper:int) =
     let count = upper - lower in
     if count <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int count - 1)
         (\k. base pow (num_of_int count - 1 - k) *
              gstr_u8 (m (lower + &k)))`;;

let gstr_svalue = new_definition
  `gstr_svalue (base:int) p (count:int) =
     gstr_svalue_sub base (gstr_bpelts p)
       (gstr_boffset p) (gstr_boffset p + count)`;;

let gstr_in_base = new_definition
  `gstr_in_base (base:int) (m:int->byte) (lower:int) (upper:int) <=>
     !k:int. lower <= k /\ k < upper
             ==> (&0:int) <= gstr_u8 (m k) /\ gstr_u8 (m k) < base`;;

let gstr_valueb = new_definition
  `gstr_valueb p (nbits:int) =
     if nbits < (&0:int) then (&0:int)
     else
       let i = nbits div (&64:int) in
       gstr_value p i +
       gstr_radix pow (num_of_int i) *
       (gstr_u64 (gstr_lpelts p (gstr_loffset p + i)) rem
        gstr_ipow (&2:int) (nbits - (&64:int) * i))`;;

let gstr_initial = new_definition
  `gstr_initial b sp up un bits sn <=>
     ((&0:int) <= (&0:int) /\ (&0:int) <= ival un) /\
     ((&0:int) <= ival sn /\ ival sn <= ival sn) /\
     (ival sn - ival sn) * gstr_u32 bits = (&0:int) /\
     ((&0:int) < ival sn ==> (&0:int) = (&64:int) * (&0:int) + (&0:int)) /\
     (((&0:int) <= (&0:int) /\ (&0:int) < (&64:int)) \/
      (word 0:int32) = un) /\
     gstr_in_base b (gstr_bpelts sp)
       (gstr_boffset sp + ival sn) (gstr_boffset sp + ival sn) /\
     ((gstr_svalue_sub b (gstr_bpelts sp)
         (gstr_boffset sp + ival sn) (gstr_boffset sp + ival sn) =
       gstr_valueb up (&0:int) /\
       (&0:int) <= (&64:int) * ival un) \/
      (ival sn = (&0:int) /\
       gstr_svalue b sp (ival sn) = gstr_value up (ival un)))`;;

let gstr_loop_inv = new_definition
  `gstr_loop_inv b sp up un bits sn shift j i sp1 <=>
     ((&0:int) <= ival i /\ ival i <= ival un) /\
     ((&0:int) <= ival j /\ ival j <= ival sn) /\
     ((&0:int) < ival j ==>
       (ival sn - ival j) * gstr_u32 bits =
       (&64:int) * ival i + gstr_u64 shift) /\
     (((&0:int) <= gstr_u64 shift /\ gstr_u64 shift < (&64:int)) \/
      i = un) /\
     gstr_in_base b (gstr_bpelts sp1)
       (gstr_boffset sp1 + ival j) (gstr_boffset sp1 + ival sn) /\
     ((gstr_svalue_sub b (gstr_bpelts sp1)
         (gstr_boffset sp1 + ival j) (gstr_boffset sp1 + ival sn) =
       gstr_valueb up ((ival sn - ival j) * gstr_u32 bits) /\
       (ival sn - ival j) * gstr_u32 bits <= (&64:int) * ival un) \/
      (ival j = (&0:int) /\
       gstr_svalue b sp1 (ival sn) = gstr_value up (ival un))) /\
     (!k:int. k < gstr_boffset sp1 \/ gstr_boffset sp1 + ival sn <= k
              ==> gstr_bpelts sp1 k = gstr_bpelts sp k)`;;

let gstr_post = new_definition
  `gstr_post b sp up un bits sn oldj newj newi newshift sp2 <=>
     ival newj < ival oldj /\
     ((&0:int) <= ival newi /\ ival newi <= ival un) /\
     ((&0:int) <= ival newj /\ ival newj <= ival sn) /\
     (ival sn - ival newj) * gstr_u32 bits =
       (ival sn - ival oldj) * gstr_u32 bits + gstr_u32 bits /\
     ((&0:int) < ival newj ==>
       (ival sn - ival oldj) * gstr_u32 bits + gstr_u32 bits =
       (&64:int) * ival newi + gstr_u64 newshift) /\
     (((&0:int) <= gstr_u64 newshift /\
       gstr_u64 newshift < (&64:int)) \/ newi = un) /\
     gstr_in_base b (gstr_bpelts sp2)
       (gstr_boffset sp2 + ival newj) (gstr_boffset sp2 + ival sn) /\
     ((gstr_svalue_sub b (gstr_bpelts sp2)
         (gstr_boffset sp2 + ival newj) (gstr_boffset sp2 + ival sn) =
       gstr_valueb up
         ((ival sn - ival oldj) * gstr_u32 bits + gstr_u32 bits) /\
       (ival sn - ival oldj) * gstr_u32 bits + gstr_u32 bits <=
         (&64:int) * ival un) \/
      (ival newj = (&0:int) /\
       gstr_svalue b sp2 (ival sn) = gstr_value up (ival un))) /\
     (!k:int. k < gstr_boffset sp2 \/ gstr_boffset sp2 + ival sn <= k
              ==> gstr_bpelts sp2 k = gstr_bpelts sp k)`;;

let gstr_store = new_definition
  `gstr_store b sp up un bits sn oldj newj newi newshift sp1 digit <=>
     ~(b = (&0:int)) /\
     gstr_uint64_in_bounds (gstr_cmod digit b) /\
     (!sj:int64.
        gstr_u64 sj = gstr_cmod digit b
        ==>
        ((&0:int) <= gstr_u64 sj /\ gstr_u64 sj <= (&255:int)) /\
        (!ch:byte.
           gstr_u8 ch = gstr_u64 sj
           ==>
           (gstr_baccess sp1 (ival newj) /\ gstr_bwritable sp1 = T) /\
           (!sp2:gstr_bptr.
              gstr_same_bframe sp2 sp1
              ==>
              gstr_bpelts sp2 =
                gstr_update (gstr_bpelts sp1)
                  (gstr_boffset sp2 + ival newj) ch /\
              gstr_bpelts sp2 (gstr_boffset sp2 + ival newj) = ch
              ==>
              gstr_post b sp up un bits sn oldj newj
                newi newshift sp2)))`;;

let gstr_cross_more = new_definition
  `gstr_cross_more b sp up un bits sn j o10 o11 sp1 o14 o15 <=>
     gstr_laccess up (ival o14) /\
     (!o16:int64.
        gstr_u64 o16 = gstr_u32 bits
        ==>
        gstr_uint64_in_bounds (gstr_u64 o16 - gstr_u64 o15) /\
        (!o17:int64.
           gstr_u64 o17 = gstr_u64 o16 - gstr_u64 o15
           ==>
           ((&0:int) <= gstr_u64 o17 /\ gstr_u64 o17 < (&64:int)) /\
           (!high:int64.
              gstr_u64 high =
                (gstr_u64 (gstr_lpelts up
                    (gstr_loffset up + ival o14)) *
                 gstr_ipow (&2:int) (gstr_u64 o17)) rem gstr_radix
              ==>
              gstr_uint64_in_bounds (gstr_u64 o11 + gstr_u64 high) /\
              (!o18:int64.
                 gstr_u64 o18 = gstr_u64 o11 + gstr_u64 high
                 ==>
                 gstr_store b sp up un bits sn j o10 o14 o15
                   sp1 (gstr_u64 o18)))))`;;

let gstr_cross = new_definition
  `gstr_cross b sp up un bits sn j i o10 o11 o13 sp1 <=>
     gstr_int32_in_bounds (ival i + (&1:int)) /\
     (!o14:int32.
        ival o14 = ival i + (&1:int)
        ==>
        if ival o14 < ival un then
          gstr_uint64_in_bounds (gstr_u64 o13 - (&64:int)) /\
          (!o15:int64.
             gstr_u64 o15 = gstr_u64 o13 - (&64:int)
             ==>
             gstr_cross_more b sp up un bits sn j o10 o11 sp1 o14 o15)
        else
          gstr_store b sp up un bits sn j o10 o14 o13
            sp1 (gstr_u64 o11))`;;

let gstr_iteration = new_definition
  `gstr_iteration b sp up un bits sn shift j i sp1 <=>
     gstr_int32_in_bounds (ival j - (&1:int)) /\
     (!o10:int32.
        ival o10 = ival j - (&1:int)
        ==>
        gstr_laccess up (ival i) /\
        ((&0:int) <= gstr_u64 shift /\ gstr_u64 shift < (&64:int)) /\
        (!o11:int64.
           gstr_u64 o11 =
             gstr_u64 (gstr_lpelts up (gstr_loffset up + ival i)) div
             gstr_ipow (&2:int) (gstr_u64 shift)
           ==>
           ~(gstr_ipow (&2:int) (gstr_u64 shift) = (&0:int)) /\
           (!o12:int64.
              gstr_u64 o12 = gstr_u32 bits
              ==>
              gstr_uint64_in_bounds
                (gstr_u64 shift + gstr_u64 o12) /\
              (!o13:int64.
                 gstr_u64 o13 = gstr_u64 shift + gstr_u64 o12
                 ==>
                 if (&64:int) <= gstr_u64 o13 then
                   gstr_cross b sp up un bits sn j i o10 o11 o13 sp1
                 else
                   gstr_store b sp up un bits sn j o10 i o13
                     sp1 (gstr_u64 o11)))))`;;

let gstr_final = new_definition
  `gstr_final sp up un bits ub sn sp1 <=>
     (&0:int) <= ival sn /\
     (!result:int32.
        gstr_u32 result = ival sn
        ==>
        gstr_in_base (gstr_ipow (&2:int) (gstr_u32 bits))
          (gstr_bpelts sp1) (gstr_boffset sp1)
          (gstr_boffset sp1 + gstr_u32 result) /\
        gstr_svalue (gstr_ipow (&2:int) (gstr_u32 bits))
          sp1 (gstr_u32 result) = gstr_value up (ival un) /\
        ((&0:int) < gstr_u32 result /\
         gstr_u32 result <=
           (ival ub + gstr_u32 bits - (&1:int)) div gstr_u32 bits) /\
        (&0:int) < gstr_u8 (gstr_bpelts sp1 (gstr_boffset sp1)) /\
        (!j1:int.
           j1 < gstr_boffset sp1 \/
           gstr_boffset sp1 +
             (ival ub + gstr_u32 bits - (&1:int)) div gstr_u32 bits <= j1
           ==> gstr_bpelts sp1 j1 = gstr_bpelts sp j1))`;;

let statement =
  `!un:int32. !up:gstr_lptr. !bits:int32. !sp:gstr_bptr. !ub:int32.
     (&1:int) <= ival un /\
     gstr_lvalid up (ival un) /\
     (&1:int) <= gstr_u32 bits /\
     gstr_u32 bits <= (&8:int) /\
     gstr_bvalid sp
       ((ival ub + gstr_u32 bits - (&1:int)) div gstr_u32 bits) /\
     (&0:int) <= ival ub /\
     gstr_value up (ival un) < gstr_ipow (&2:int) (ival ub) /\
     (&0:int) <
       gstr_u64 (gstr_lpelts up
         (gstr_loffset up + ival un - (&1:int))) /\
     (&64:int) * ival un + (&7:int) <= (&2147483647:int) /\
     gstr_bwritable sp = T
     ==>
     gstr_int32_in_bounds (ival un - (&1:int)) /\
     (!o1:int32.
        ival o1 = ival un - (&1:int)
        ==>
        gstr_laccess up (ival o1) /\
        (let um = gstr_lpelts up (gstr_loffset up + ival o1) in
         (&0:int) < gstr_u64 um /\
         (!sb:int64.
            (((&1:int) <= gstr_u64 sb /\ gstr_u64 sb <= (&64:int)) /\
             gstr_ipow (&2:int) (gstr_u64 sb - (&1:int)) <= gstr_u64 um /\
             gstr_u64 um < gstr_ipow (&2:int) (gstr_u64 sb))
            ==>
            gstr_u32 bits <= (&2147483647:int) /\
            (!o2:int32.
               ival o2 = gstr_u32 bits
               ==>
               gstr_u64 sb <= (&2147483647:int) /\
               (!o3:int32.
                  ival o3 = gstr_u64 sb
                  ==>
                  gstr_int32_in_bounds (ival un - (&1:int)) /\
                  (!o4:int32.
                     ival o4 = ival un - (&1:int)
                     ==>
                     gstr_int32_in_bounds ((&64:int) * ival o4) /\
                     (!o5:int32.
                        ival o5 = (&64:int) * ival o4
                        ==>
                        gstr_int32_in_bounds (ival o5 + ival o3) /\
                        (!o6:int32.
                           ival o6 = ival o5 + ival o3
                           ==>
                           gstr_int32_in_bounds (ival o6 + ival o2) /\
                           (!o7:int32.
                              ival o7 = ival o6 + ival o2
                              ==>
                              gstr_int32_in_bounds
                                (ival o7 - (&1:int)) /\
                              (!e:int32.
                                 ival e = ival o7 - (&1:int)
                                 ==>
                                 gstr_u32 bits <= (&2147483647:int) /\
                                 (!o8:int32.
                                    ival o8 = gstr_u32 bits
                                    ==>
                                    (~(ival o8 = (&0:int)) /\
                                     gstr_int32_in_bounds
                                       (gstr_cdiv (ival e) (ival o8))) /\
                                    (!sn:int32.
                                       ival sn =
                                         gstr_cdiv (ival e) (ival o8)
                                       ==>
                                       (!o9:int64.
                                          gstr_u64 o9 = gstr_u32 bits
                                          ==>
                                          (((&0:int) <= gstr_u64 o9 /\
                                            gstr_u64 o9 < (&64:int)) /\
                                           gstr_ipow (&2:int)
                                             (gstr_u64 o9) *
                                             gstr_u64 (word 1:int64) <=
                                             (&18446744073709551615:int)) /\
                                          (!b:int64.
                                             gstr_u64 b =
                                               gstr_ipow (&2:int)
                                                 (gstr_u64 o9) *
                                               gstr_u64 (word 1:int64)
                                             ==>
                                             gstr_initial
                                               (gstr_u64 b) sp up un
                                               bits sn /\
                                             (!shift:int64. !j:int32.
                                              !i:int32. !sp1:gstr_bptr.
                                                gstr_same_bframe sp1 sp
                                                ==>
                                                gstr_loop_inv
                                                  (gstr_u64 b) sp up un
                                                  bits sn shift j i sp1
                                                ==>
                                                if (&0:int) < ival j then
                                                  gstr_iteration
                                                    (gstr_u64 b) sp up un
                                                    bits sn shift j i sp1
                                                else
                                                  gstr_final
                                                    sp up un bits ub sn
                                                    sp1)))))))))))))))`;;
