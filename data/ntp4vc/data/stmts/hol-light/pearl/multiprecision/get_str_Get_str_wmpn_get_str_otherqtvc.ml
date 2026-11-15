(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/get_str_Get_str_wmpn_get_str_otherqtvc: the verification
  condition for converting a positive multiprecision integer to digits in an
  arbitrary base, including normalized division, zero padding, byte reversal,
  pointer frames, and the final string-value contract. This file contains no
  proof.
*)

let gso_output = open_out "/dev/null";;
Format.pp_set_formatter_out_channel Format.std_formatter gso_output;;

needs "Library/words.ml";;
needs "Library/isum.ml";;

new_type_abbrev
  ("gso_lptr",`:(int64 list)#(int#(int#(int#(bool#Z))))`);;
new_type_abbrev
  ("gso_bptr",`:(byte list)#(int#(int#(int#(bool#Z))))`);;
new_type_abbrev ("gso_info",`:int#(int32#int64)`);;

let gso_radix = new_definition
  `gso_radix = (&18446744073709551616:int)`;;
let gso_u64 = new_definition `gso_u64 (x:int64) = (&(val x):int)`;;
let gso_u32 = new_definition `gso_u32 (x:int32) = (&(val x):int)`;;
let gso_u8 = new_definition
  `gso_u8 (x:byte) = (&(val x):int)`;;
let gso_i32 = new_definition `gso_i32 (x:int32) = ival x`;;
let gso_i32_bounds = new_definition
  `gso_i32_bounds (x:int) <=>
     --(&2147483648:int) <= x /\ x <= (&2147483647:int)`;;
let gso_u32_bounds = new_definition
  `gso_u32_bounds (x:int) <=>
     (&0:int) <= x /\ x <= (&4294967295:int)`;;
let gso_ipow = new_definition
  `gso_ipow (b:int) (e:int) =
     b pow (if e < (&0:int) then 0 else num_of_int e)`;;

let gso_ldata = new_definition `gso_ldata (p:gso_lptr) = FST p`;;
let gso_bdata = new_definition `gso_bdata (p:gso_bptr) = FST p`;;
let gso_loff = new_definition `gso_loff (p:gso_lptr) = FST (SND p)`;;
let gso_boff = new_definition `gso_boff (p:gso_bptr) = FST (SND p)`;;
let gso_lmin = new_definition
  `gso_lmin (p:gso_lptr) = FST (SND (SND p))`;;
let gso_bmin = new_definition
  `gso_bmin (p:gso_bptr) = FST (SND (SND p))`;;
let gso_lmax = new_definition
  `gso_lmax (p:gso_lptr) = FST (SND (SND (SND p)))`;;
let gso_bmax = new_definition
  `gso_bmax (p:gso_bptr) = FST (SND (SND (SND p)))`;;
let gso_lwrite = new_definition
  `gso_lwrite (p:gso_lptr) = FST (SND (SND (SND (SND p))))`;;
let gso_bwrite = new_definition
  `gso_bwrite (p:gso_bptr) = FST (SND (SND (SND (SND p))))`;;
let gso_lzone = new_definition
  `gso_lzone (p:gso_lptr) = SND (SND (SND (SND (SND p))))`;;
let gso_bzone = new_definition
  `gso_bzone (p:gso_bptr) = SND (SND (SND (SND (SND p))))`;;

let gso_lpelts = new_definition
  `gso_lpelts p (i:int) =
     let k = if i < (&0:int) then 0 else num_of_int i in
     if k < LENGTH (gso_ldata p) then EL k (gso_ldata p)
     else (word 0:int64)`;;
let gso_bpelts = new_definition
  `gso_bpelts p (i:int) =
     let k = if i < (&0:int) then 0 else num_of_int i in
     if k < LENGTH (gso_bdata p) then EL k (gso_bdata p)
     else (word 0:byte)`;;

let gso_lvalid = new_definition
  `gso_lvalid p (n:int) <=>
     gso_i32_bounds n /\ (&0:int) <= n /\
     (&0:int) <= gso_lmin p /\ gso_lmin p <= gso_loff p /\
     gso_loff p + n <= gso_lmax p /\
     gso_lmax p <= (&(LENGTH (gso_ldata p)):int)`;;
let gso_bvalid = new_definition
  `gso_bvalid p (n:int) <=>
     gso_i32_bounds n /\ (&0:int) <= n /\
     (&0:int) <= gso_bmin p /\ gso_bmin p <= gso_boff p /\
     gso_boff p + n <= gso_bmax p /\
     gso_bmax p <= (&(LENGTH (gso_bdata p)):int)`;;
let gso_laccess = new_definition
  `gso_laccess p (i:int) <=> gso_lmin p <= i /\ i < gso_lmax p`;;
let gso_baccess = new_definition
  `gso_baccess p (i:int) <=> gso_bmin p <= i /\ i < gso_bmax p`;;

let gso_same_lframe = new_definition
  `gso_same_lframe newer older <=>
     LENGTH (gso_ldata newer) = LENGTH (gso_ldata older) /\
     gso_loff newer = gso_loff older /\
     gso_lmin newer = gso_lmin older /\
     gso_lmax newer = gso_lmax older /\
     gso_lwrite newer = gso_lwrite older /\
     gso_lzone newer = gso_lzone older`;;
let gso_same_bframe = new_definition
  `gso_same_bframe newer older <=>
     LENGTH (gso_bdata newer) = LENGTH (gso_bdata older) /\
     gso_boff newer = gso_boff older /\
     gso_bmin newer = gso_bmin older /\
     gso_bmax newer = gso_bmax older /\
     gso_bwrite newer = gso_bwrite older /\
     gso_bzone newer = gso_bzone older`;;
let gso_shifted = new_definition
  `gso_shifted shifted original (n:int) <=>
     gso_boff shifted = gso_boff original + n /\
     LENGTH (gso_bdata shifted) = LENGTH (gso_bdata original) /\
     gso_bdata shifted = gso_bdata original /\
     gso_bmin shifted = gso_bmin original /\
     gso_bmax shifted = gso_bmax original /\
     gso_bzone shifted = gso_bzone original /\
     gso_bwrite shifted = gso_bwrite original`;;
let gso_update = new_definition
  `gso_update (f:int->A) (i:int) (x:A) =
     \j. if j = i then x else f j`;;

let gso_value = new_definition
  `gso_value p (n:int) =
     if n <= (&0:int) then (&0:int)
     else isum (0..num_of_int n - 1)
       (\k. gso_radix pow k *
            gso_u64 (gso_lpelts p (gso_loff p + &k)))`;;
let gso_svalue_le_sub = new_definition
  `gso_svalue_le_sub (b:int) (m:int->byte) (lo:int) (hi:int) =
     let n = hi - lo in
     if n <= (&0:int) then (&0:int)
     else isum (0..num_of_int n - 1)
       (\k. b pow k * gso_u8 (m (lo + &k)))`;;
let gso_svalue_le = new_definition
  `gso_svalue_le (b:int) p (n:int) =
     gso_svalue_le_sub b (gso_bpelts p) (gso_boff p) (gso_boff p + n)`;;
let gso_svalue_sub = new_definition
  `gso_svalue_sub (b:int) (m:int->byte) (lo:int) (hi:int) =
     let n = hi - lo in
     if n <= (&0:int) then (&0:int)
     else isum (0..num_of_int n - 1)
       (\k. b pow (num_of_int n - 1 - k) * gso_u8 (m (lo + &k)))`;;
let gso_svalue = new_definition
  `gso_svalue (b:int) p (n:int) =
     gso_svalue_sub b (gso_bpelts p) (gso_boff p) (gso_boff p + n)`;;
let gso_in_base = new_definition
  `gso_in_base (b:int) (m:int->byte) (lo:int) (hi:int) <=>
     !i:int. lo <= i /\ i < hi ==> (&0:int) <= gso_u8 (m i) /\
                                      gso_u8 (m i) < b`;;
let gso_bframe = new_definition
  `gso_bframe newer older (n:int) <=>
     !i:int. i < gso_boff newer \/ gso_boff newer + n <= i
             ==> gso_bpelts newer i = gso_bpelts older i`;;
let gso_lframe = new_definition
  `gso_lframe newer older (n:int) <=>
     !i:int. i < gso_loff newer \/ gso_loff newer + n <= i
             ==> gso_lpelts newer i = gso_lpelts older i`;;
let gso_map_eq = new_definition
  `gso_map_eq x y (xi:int) (yi:int) (n:int) <=>
     !i:int. (&0:int) <= i /\ i < n
             ==> gso_lpelts x (xi + i) = gso_lpelts y (yi + i)`;;

let gso_info_b = new_definition `gso_info_b (q:gso_info) = FST q`;;
let gso_info_exp = new_definition `gso_info_exp (q:gso_info) = FST (SND q)`;;
let gso_info_bb = new_definition `gso_info_bb (q:gso_info) = SND (SND q)`;;
let gso_info_ok = new_definition
  `gso_info_ok q <=>
     (&2:int) <= gso_info_b q /\ gso_info_b q <= (&256:int) /\
     gso_u64 (gso_info_bb q) < gso_radix /\
     gso_radix <= gso_u64 (gso_info_bb q) * gso_info_b q /\
     (&7:int) <= gso_u32 (gso_info_exp q) /\
     gso_u32 (gso_info_exp q) <= (&63:int) /\
     gso_u64 (gso_info_bb q) =
       gso_ipow (gso_info_b q) (gso_u32 (gso_info_exp q))`;;
let gso_reciprocal = new_definition
  `gso_reciprocal di d1 <=>
     gso_u64 di =
       ((gso_radix * gso_radix - (&1:int)) div gso_u64 d1) -
       gso_radix`;;
let gso_division = new_definition
  `gso_division quotient dividend count divisor remainder <=>
     gso_value dividend (gso_i32 count) =
       gso_value quotient (gso_i32 count) * gso_u64 divisor +
       gso_u64 remainder /\
     gso_u64 remainder < gso_u64 divisor`;;
let gso_allocated = new_definition
  `gso_allocated p (n:int) <=>
     (&(LENGTH (gso_ldata p)):int) = n /\
     gso_loff p = (&0:int) /\ gso_lmin p = (&0:int) /\
     gso_lmax p = n /\ gso_lwrite p = T`;;

let gso_limb_post = new_definition
  `gso_limb_post b before after capacity input done <=>
     gso_svalue_le b after (gso_u32 done) = gso_u64 input /\
     ((&0:int) <= gso_u32 done /\ gso_u32 done <= capacity) /\
     ((&0:int) < gso_u32 done ==>
       (&0:int) < gso_u8 (gso_bpelts after
         (gso_boff after + gso_u32 done - (&1:int)))) /\
     gso_bframe after before (gso_u32 done) /\
     gso_in_base b (gso_bpelts after) (gso_boff after)
       (gso_boff after + gso_u32 done)`;;
let gso_partial = new_definition
  `gso_partial total b original_sp size up current_sp sn <=>
     gso_svalue_le b current_sp (gso_i32 sn) +
       gso_ipow b (gso_i32 sn) * gso_value up (&1:int) = total /\
     gso_in_base b (gso_bpelts current_sp) (gso_boff current_sp)
       (gso_boff current_sp + gso_i32 sn) /\
     ((&0:int) <= gso_i32 sn /\ gso_i32 sn < gso_i32 size) /\
     (&0:int) < gso_value up (&1:int) /\
     gso_bframe current_sp original_sp (gso_i32 size)`;;
let gso_outer_inv = new_definition
  `gso_outer_inv total b info un size original_sp loopi up n sp sn <=>
     gso_svalue_le b sp (gso_i32 sn) +
       gso_ipow b (gso_i32 sn) * gso_value up (gso_i32 n) = total /\
     ((&1:int) <= gso_i32 n /\ gso_i32 n <= gso_i32 un) /\
     gso_i32 un - gso_i32 n <= loopi /\
     ((&0:int) <= gso_i32 sn /\ gso_i32 sn < gso_i32 size) /\
     gso_i32 sn = loopi * gso_u32 (gso_info_exp info) /\
     gso_in_base b (gso_bpelts sp) (gso_boff sp)
       (gso_boff sp + gso_i32 sn) /\
     (&0:int) < gso_u64 (gso_lpelts up
       (gso_loff up + gso_i32 n - (&1:int))) /\
     gso_bframe sp original_sp (gso_i32 size)`;;
let gso_padding_inv = new_definition
  `gso_padding_inv total b info size original_sp up n initial_sn
                   done current_sn sp <=>
     gso_u32 done <= gso_u32 (gso_info_exp info) /\
     gso_i32 current_sn = gso_i32 initial_sn + gso_u32 done /\
     gso_in_base b (gso_bpelts sp) (gso_boff sp)
       (gso_boff sp + gso_i32 current_sn) /\
     gso_svalue_le b sp (gso_i32 current_sn) +
       gso_ipow b
         (gso_i32 current_sn - gso_u32 done +
          gso_u32 (gso_info_exp info)) *
       gso_value up (gso_i32 n) = total /\
     gso_bframe sp original_sp (gso_i32 size)`;;

let gso_reverse_inv = new_definition
  `gso_reverse_inv b size original_sp reversal_original current total i <=>
     ((&0:int) <= (&2:int) * gso_i32 i + (&1:int) /\
      (&2:int) * gso_i32 i + (&1:int) <= gso_i32 total + (&1:int)) /\
     (!j:int. gso_boff current + gso_i32 i <= j /\
              j < gso_boff current + gso_i32 total - gso_i32 i
              ==> gso_bpelts current j = gso_bpelts reversal_original j) /\
     gso_in_base b (gso_bpelts current) (gso_boff current)
       (gso_boff current + gso_i32 total) /\
     gso_svalue_sub b (gso_bpelts current) (gso_boff current)
       (gso_boff current + gso_i32 i) =
       gso_svalue_le_sub b (gso_bpelts reversal_original)
         (gso_boff current + gso_i32 total - gso_i32 i)
         (gso_boff current + gso_i32 total) /\
     gso_svalue_sub b (gso_bpelts current)
       (gso_boff current + gso_i32 total - gso_i32 i)
       (gso_boff current + gso_i32 total) =
       gso_svalue_le_sub b (gso_bpelts reversal_original)
         (gso_boff current) (gso_boff current + gso_i32 i) /\
     gso_svalue_le_sub b (gso_bpelts current)
       (gso_boff current + gso_i32 i)
       (gso_boff current + gso_i32 total - gso_i32 i) =
       gso_svalue_le_sub b (gso_bpelts reversal_original)
         (gso_boff current + gso_i32 i)
         (gso_boff current + gso_i32 total - gso_i32 i) /\
     ((&0:int) < gso_i32 i ==>
       (&0:int) < gso_u8 (gso_bpelts current (gso_boff current))) /\
     gso_bframe current original_sp (gso_i32 size)`;;
let gso_final_post = new_definition
  `gso_final_post b original_up un original_sp size current result <=>
     ((&0:int) <= gso_u32 result /\ gso_u32 result < gso_i32 size) /\
     gso_svalue b current (gso_u32 result) =
       gso_value original_up (gso_i32 un) /\
     gso_in_base b (gso_bpelts current) (gso_boff current)
       (gso_boff current + gso_u32 result) /\
     (&0:int) < gso_u8 (gso_bpelts current (gso_boff current)) /\
     gso_bframe current original_sp (gso_i32 size)`;;

let gso_reverse_swap = new_definition
  `gso_reverse_swap b size original_sp rev total current i <=>
     gso_baccess current (gso_boff current + gso_i32 i) /\
           (!saved:byte.
              saved = gso_bpelts current (gso_boff current + gso_i32 i)
              ==> gso_i32_bounds (gso_i32 total - gso_i32 i) /\
              (!from_end:int32.
                 gso_i32 from_end = gso_i32 total - gso_i32 i
                 ==> gso_i32_bounds (gso_i32 from_end - (&1:int)) /\
                 (!mirror:int32.
                    gso_i32 mirror = gso_i32 from_end - (&1:int)
                    ==> gso_baccess current
                          (gso_boff current + gso_i32 mirror) /\
                        (!other:byte.
                           other = gso_bpelts current
                             (gso_boff current + gso_i32 mirror)
                           ==> (gso_baccess current
                                  (gso_boff current + gso_i32 i) /\
                                gso_bwrite current = T) /\
                               (!after1:gso_bptr.
                                  gso_same_bframe after1 current /\
                                  gso_bpelts after1 =
                                    gso_update (gso_bpelts current)
                                      (gso_boff after1 + gso_i32 i) other /\
                                  gso_bpelts after1
                                    (gso_boff after1 + gso_i32 i) = other
                                  ==> gso_i32_bounds
                                        (gso_i32 total - gso_i32 i) /\
                                      (!from_end2:int32.
                                         gso_i32 from_end2 =
                                           gso_i32 total - gso_i32 i
                                         ==> gso_i32_bounds
                                               (gso_i32 from_end2 - (&1:int)) /\
                                             (!mirror2:int32.
                                                gso_i32 mirror2 =
                                                  gso_i32 from_end2 - (&1:int)
                                                ==> (gso_baccess after1
                                                       (gso_boff after1 +
                                                        gso_i32 mirror2) /\
                                                     gso_bwrite after1 = T) /\
                                                    (!after2:gso_bptr.
                                                       gso_same_bframe
                                                         after2 after1 /\
                                                       gso_bpelts after2 =
                                                         gso_update
                                                           (gso_bpelts after1)
                                                           (gso_boff after2 +
                                                            gso_i32 mirror2)
                                                           saved /\
                                                       gso_bpelts after2
                                                         (gso_boff after2 +
                                                          gso_i32 mirror2) =
                                                         saved
                                                       ==> gso_i32_bounds
                                                             (gso_i32 i +
                                                              (&1:int)) /\
                                                           (!next_i:int32.
                                                              gso_i32 next_i =
                                                                gso_i32 i +
                                                                (&1:int)
                                                              ==> ((&0:int) <=
                                                                   gso_i32 total -
                                                                   gso_i32 i /\
                                                                   gso_i32 total -
                                                                   gso_i32 next_i <
                                                                   gso_i32 total -
                                                                   gso_i32 i) /\
                                                                  gso_reverse_inv
                                                                    b size
                                                                    original_sp
                                                                    rev after2
                                                                    total
                                                                    next_i)))))))))`;;

let gso_reverse_step = new_definition
  `gso_reverse_step b original_up un original_sp size rev total current i <=>
     gso_i32_bounds ((&2:int) * gso_i32 i) /\
     (!twice:int32. gso_i32 twice = (&2:int) * gso_i32 i ==>
       gso_i32_bounds (gso_i32 twice + (&1:int)) /\
       (!test:int32. gso_i32 test = gso_i32 twice + (&1:int) ==>
         (gso_i32 test < gso_i32 total
          ==> gso_reverse_swap b size original_sp rev total current i) /\
         (~(gso_i32 test < gso_i32 total)
          ==> (&0:int) <= gso_i32 total /\
              (!result:int32. gso_u32 result = gso_i32 total
                ==> gso_final_post b original_up un original_sp size
                      current result))))`;;

let gso_reverse_loop = new_definition
  `gso_reverse_loop b original_up un original_sp size rev total <=>
     gso_reverse_inv b size original_sp rev rev total (word 0:int32) /\
     (!i:int32. !current:gso_bptr.
        gso_same_bframe current rev /\
        gso_reverse_inv b size original_sp rev current total i
        ==> gso_reverse_step b original_up un original_sp size rev
              total current i)`;;

let gso_final_limb = new_definition
  `gso_final_limb b original_up un info original_sp size shift d1 di
                  current_up current_sp sn <=>
     gso_laccess current_up (gso_loff current_up) /\
     (!last:int64.
        last = gso_lpelts current_up (gso_loff current_up)
        ==> (gso_bmin current_sp <= gso_boff current_sp + gso_i32 sn /\
             gso_boff current_sp + gso_i32 sn <= gso_bmax current_sp) /\
            (!spn:gso_bptr.
               gso_shifted spn current_sp (gso_i32 sn)
               ==> gso_i32_bounds (gso_i32 size - (&1:int)) /\
                   (!size1:int32.
                      gso_i32 size1 = gso_i32 size - (&1:int)
                      ==> gso_i32_bounds (gso_i32 size1 - gso_i32 sn) /\
                          (!capacity:int32.
                             gso_i32 capacity =
                               gso_i32 size1 - gso_i32 sn
                             ==> (((&2:int) <= gso_info_b info /\
                                   gso_info_b info <= (&256:int)) /\
                                  gso_bwrite spn = T /\
                                  gso_radix div (&2:int) <= gso_u64 d1 /\
                                  ((&0:int) <= gso_u64 shift /\
                                   gso_u64 shift <= (&63:int)) /\
                                  gso_info_b info *
                                    gso_ipow (&2:int) (gso_u64 shift) =
                                    gso_u64 d1 /\
                                  gso_reciprocal di d1 /\
                                  gso_bvalid spn (gso_i32 capacity) /\
                                  (&0:int) < gso_i32 capacity /\
                                  gso_u64 last <
                                    gso_ipow (gso_info_b info)
                                      (gso_i32 capacity)) /\
                                 (!after_local:gso_bptr.
                                  !returned:gso_bptr.
                                    gso_bpelts after_local =
                                      gso_bpelts returned /\
                                    gso_same_bframe after_local spn /\
                                    gso_same_bframe returned current_sp
                                    ==> (!done:int32.
                                          gso_limb_post
                                            (gso_info_b info) spn after_local
                                            (gso_i32 capacity) last done
                                          ==> gso_u32 done <=
                                                (&2147483647:int) /\
                                              (!done_i:int32.
                                                 gso_i32 done_i =
                                                   gso_u32 done
                                                 ==> gso_i32_bounds
                                                       (gso_i32 sn +
                                                        gso_i32 done_i) /\
                                                     (!total:int32.
                                                        gso_i32 total =
                                                          gso_i32 sn +
                                                          gso_i32 done_i
                                                        ==> gso_reverse_loop
                                                              b original_up un
                                                              original_sp size
                                                              returned
                                                              total))))))))`;;

let gso_final_cont = new_definition
  `gso_final_cont total b original_up un info original_sp size shift d1 di <=>
     !sn:int32. !up:gso_lptr. !sp:gso_bptr.
       gso_same_lframe up original_up /\
       gso_same_bframe sp original_sp /\
       gso_partial total b original_sp size up sp sn
       ==> gso_final_limb b original_up un info original_sp size shift d1 di
             up sp sn`;;

let gso_padding_step = new_definition
  `gso_padding_step total b info original_sp size un up n initial_sn
                    done sp current_sn previous_up previous_n loopi <=>
     if gso_u32 done < gso_u32 (gso_info_exp info) then
       (gso_baccess sp (gso_boff sp + gso_i32 current_sn) /\
        gso_bwrite sp = T) /\
       (!after:gso_bptr.
          gso_same_bframe after sp /\
          gso_bpelts after =
            gso_update (gso_bpelts sp)
              (gso_boff after + gso_i32 current_sn) (word 0:byte) /\
          gso_bpelts after (gso_boff after + gso_i32 current_sn) =
            (word 0:byte)
          ==> gso_i32_bounds (gso_i32 current_sn + (&1:int)) /\
              (!next_sn:int32.
                 gso_i32 next_sn = gso_i32 current_sn + (&1:int)
                 ==> gso_u32_bounds (gso_u32 done + (&1:int)) /\
                     (!next_done:int32.
                        gso_u32 next_done = gso_u32 done + (&1:int)
                        ==> ((&0:int) <=
                               gso_u32 (gso_info_exp info) - gso_u32 done /\
                             gso_u32 (gso_info_exp info) -
                               gso_u32 next_done <
                             gso_u32 (gso_info_exp info) - gso_u32 done) /\
                            gso_padding_inv total b info size original_sp
                              up n initial_sn next_done next_sn after)))
     else
       ((&0:int) <= gso_value previous_up (gso_i32 previous_n) /\
        gso_value up (gso_i32 n) <
          gso_value previous_up (gso_i32 previous_n)) /\
       gso_outer_inv total b info un size original_sp (loopi + (&1:int))
         up n sp current_sn`;;

let gso_after_limb = new_definition
  `gso_after_limb total b info original_sp before_sp size un shift d1 di
                  up n initial_sn input previous_up previous_n loopi spn <=>
     gso_u32 (gso_info_exp info) <= (&2147483647:int) /\
     (!signed_exp:int32.
        gso_i32 signed_exp = gso_u32 (gso_info_exp info)
        ==> gso_i32_bounds (gso_i32 signed_exp + (&1:int)) /\
            (!capacity:int32.
               gso_i32 capacity = gso_i32 signed_exp + (&1:int)
               ==> (((&2:int) <= gso_info_b info /\
                     gso_info_b info <= (&256:int)) /\
                    gso_bwrite spn = T /\
                    gso_radix div (&2:int) <= gso_u64 d1 /\
                    ((&0:int) <= gso_u64 shift /\
                     gso_u64 shift <= (&63:int)) /\
                    gso_info_b info * gso_ipow (&2:int) (gso_u64 shift) =
                      gso_u64 d1 /\
                    gso_reciprocal di d1 /\
                    gso_bvalid spn (gso_i32 capacity) /\
                    (&0:int) < gso_i32 capacity /\
                    gso_u64 input <
                      gso_ipow (gso_info_b info) (gso_i32 capacity)) /\
                   (!after_local:gso_bptr. !returned:gso_bptr.
                      gso_bpelts after_local = gso_bpelts returned /\
                      gso_same_bframe after_local spn /\
                      gso_same_bframe returned before_sp
                      ==> (!done:int32.
                            gso_limb_post (gso_info_b info) spn after_local
                              (gso_i32 capacity) input done
                            ==> gso_u32 done <= (&2147483647:int) /\
                                (!done_i:int32.
                                   gso_i32 done_i = gso_u32 done
                                   ==> gso_i32_bounds
                                         (gso_i32 initial_sn +
                                          gso_i32 done_i) /\
                                       (!new_sn:int32.
                                          gso_i32 new_sn =
                                            gso_i32 initial_sn +
                                            gso_i32 done_i
                                          ==> gso_padding_inv total b info
                                                size original_sp up n
                                                initial_sn done new_sn
                                                returned /\
                                              (!loop_done:int32.
                                               !loop_sn:int32.
                                               !loop_sp:gso_bptr.
                                                 gso_same_bframe
                                                   loop_sp returned /\
                                                 gso_padding_inv total b info
                                                   size original_sp up n
                                                   initial_sn loop_done
                                                   loop_sn loop_sp
                                                 ==> gso_padding_step total b
                                                       info original_sp size un
                                                       up n initial_sn
                                                       loop_done loop_sp
                                                       loop_sn previous_up
                                                       previous_n
                                                       loopi)))))))`;;

let gso_outer_step = new_definition
  `gso_outer_step total b info original_sp size original_up un shift d1 di
                  temporary up n sp sn loopi <=>
     if (&1:int) < gso_i32 n then
       (gso_lvalid up (gso_i32 n) /\
        gso_lvalid temporary (gso_i32 n) /\
        gso_lwrite temporary = T /\
        (&0:int) < gso_i32 n /\
        (&0:int) < gso_u64 (gso_info_bb info)) /\
       (!after_div:gso_lptr.
          gso_same_lframe after_div temporary
          ==> (!remainder:int64.
                gso_division after_div up n (gso_info_bb info) remainder
                ==> gso_lvalid after_div (gso_i32 n) /\
                    gso_lvalid up (gso_i32 n) /\ gso_lwrite up = T /\
                    (!copied:gso_lptr.
                       gso_same_lframe copied up /\
                       gso_map_eq copied after_div (gso_loff copied)
                         (gso_loff after_div) (gso_i32 n) /\
                       gso_lframe copied up (gso_i32 n)
                       ==> gso_i32_bounds (gso_i32 n - (&1:int)) /\
                           (!n1:int32.
                              gso_i32 n1 = gso_i32 n - (&1:int)
                              ==> gso_laccess copied
                                    (gso_loff copied + gso_i32 n1) /\
                                  (!top:int64.
                                     top = gso_lpelts copied
                                       (gso_loff copied + gso_i32 n1)
                                     ==> (!is_zero:bool.
                                           (gso_u64 top = (&0:int)
                                            ==> is_zero = T) /\
                                           (is_zero = T
                                            ==> top = (word 0:int64))
                                           ==> (!dec:int32.
                                                 (if is_zero
                                                  then dec = (word 1:int32)
                                                  else dec = (word 0:int32))
                                                 ==> gso_i32_bounds
                                                       (gso_i32 n -
                                                        gso_i32 dec) /\
                                                     (!next_n:int32.
                                                        gso_i32 next_n =
                                                          gso_i32 n -
                                                          gso_i32 dec
                                                        ==> (gso_bmin sp <=
                                                             gso_boff sp +
                                                             gso_i32 sn /\
                                                             gso_boff sp +
                                                             gso_i32 sn <=
                                                             gso_bmax sp) /\
                                                            (!spn:gso_bptr.
                                                               gso_shifted spn
                                                                 sp (gso_i32 sn)
                                                               ==> gso_after_limb
                                                                     total b info
                                                                     original_sp
                                                                     sp size un
                                                                     shift d1 di
                                                                     copied next_n
                                                                     sn remainder
                                                                     up n loopi
                                                                     spn)))))))))
     else gso_partial total b original_sp size up sp sn`;;

let gso_partial_block = new_definition
  `gso_partial_block total b info original_up un original_sp size shift d1 di <=>
     if (&1:int) < gso_i32 un then
       (&0:int) <= gso_i32 un /\
       (!count:int32.
          gso_u32 count = gso_i32 un
          ==> (&0:int) <= gso_u32 count /\
              (!temporary:gso_lptr.
                 gso_allocated temporary (gso_u32 count)
                 ==> gso_outer_inv total b info un size original_sp (&0:int)
                       original_up un original_sp (word 0:int32) /\
                     (!loopi:int. !loop_tmp:gso_lptr. !loop_up:gso_lptr.
                      !loop_n:int32. !loop_sp:gso_bptr. !loop_sn:int32.
                        gso_same_lframe loop_tmp temporary /\
                        gso_same_lframe loop_up original_up /\
                        gso_same_bframe loop_sp original_sp /\
                        gso_outer_inv total b info un size original_sp loopi
                          loop_up loop_n loop_sp loop_sn
                        ==> gso_outer_step total b info original_sp size
                              original_up un shift d1 di loop_tmp loop_up
                              loop_n loop_sp loop_sn loopi)))
     else
       gso_partial total b original_sp size original_up original_sp
         (word 0:int32)`;;

let gso_body = new_definition
  `gso_body total original_up un b info original_sp size shift d1 di <=>
     gso_partial_block total b info original_up un original_sp size shift d1 di /\
     gso_final_cont total b original_up un info original_sp size shift d1 di`;;

let statement =
  `!up:gso_lptr. !un:int32. !base:int32. !info:gso_info.
   !sp:gso_bptr. !size:int32.
     gso_info_ok info /\
     gso_lvalid up (gso_i32 un) /\
     (&1:int) <= gso_i32 un /\
     gso_info_b info = gso_i32 base /\
     gso_lwrite up = T /\ gso_bwrite sp = T /\
     (&0:int) < gso_u64 (gso_lpelts up
       (gso_loff up + gso_i32 un - (&1:int))) /\
     (&0:int) < gso_i32 size /\
     gso_bvalid sp (gso_i32 size) /\
     gso_value up (gso_i32 un) <
       gso_ipow (gso_i32 base) (gso_i32 size - (&1:int))
     ==>
     (&0:int) <= gso_i32 base /\
     (!base_limb:int64.
        gso_u64 base_limb = gso_i32 base
        ==> (&0:int) < gso_u64 base_limb /\
            (!count:int32.
               gso_ipow (&2:int) (gso_i32 count) * gso_u64 base_limb <=
                 (&18446744073709551615:int) /\
               (&18446744073709551615:int) <
                 (&2:int) * gso_ipow (&2:int) (gso_i32 count) *
                 gso_u64 base_limb /\
               (&0:int) <= gso_i32 count /\ gso_i32 count < (&64:int)
               ==> (&0:int) <= gso_i32 count /\
                   (!shift:int64.
                      gso_u64 shift = gso_i32 count
                      ==> (&0:int) <= gso_i32 base /\
                          (!base_limb2:int64.
                             gso_u64 base_limb2 = gso_i32 base
                             ==> (((&0:int) <= gso_u64 shift /\
                                   gso_u64 shift < (&64:int)) /\
                                  gso_ipow (&2:int) (gso_u64 shift) *
                                    gso_u64 base_limb2 <=
                                    (&18446744073709551615:int)) /\
                                 (!d1:int64.
                                    gso_u64 d1 =
                                      gso_ipow (&2:int) (gso_u64 shift) *
                                      gso_u64 base_limb2
                                    ==> gso_radix div (&2:int) <=
                                          gso_u64 d1 /\
                                        (!di:int64.
                                           gso_reciprocal di d1
                                           ==> gso_body
                                                 (gso_value up (gso_i32 un))
                                                 up un (gso_i32 base) info sp
                                                 size shift d1 di))))))`;;

Format.pp_print_flush Format.std_formatter ();;
Format.pp_set_formatter_out_channel Format.std_formatter stdout;;
close_out gso_output;;
