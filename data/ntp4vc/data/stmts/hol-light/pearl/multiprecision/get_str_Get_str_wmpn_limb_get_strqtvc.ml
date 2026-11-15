(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/get_str_Get_str_wmpn_limb_get_strqtvc: the loop
  verification condition for converting one 64-bit limb into little-endian
  base digits, including reciprocal division, byte storage, invariants,
  pointer frames, and the final digit-string contract. This file contains no
  proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

new_type_abbrev
  ("gsl_bptr",`:(byte list)#(int#(int#(int#(bool#Z))))`);;
new_type_abbrev ("gsl_info",`:int#(int32#int64)`);;

let gsl_radix = new_definition
  `gsl_radix = (&18446744073709551616:int)`;;
let gsl_u64 = new_definition `gsl_u64 (x:int64) = (&(val x):int)`;;
let gsl_u32 = new_definition `gsl_u32 (x:int32) = (&(val x):int)`;;
let gsl_u8 = new_definition `gsl_u8 (x:byte) = (&(val x):int)`;;
let gsl_i32 = new_definition `gsl_i32 (x:int32) = ival x`;;
let gsl_i32_bounds = new_definition
  `gsl_i32_bounds (x:int) <=>
     --(&2147483648:int) <= x /\ x <= (&2147483647:int)`;;
let gsl_u64_bounds = new_definition
  `gsl_u64_bounds (x:int) <=>
     (&0:int) <= x /\ x <= (&18446744073709551615:int)`;;
let gsl_ipow = new_definition
  `gsl_ipow (b:int) (e:int) =
     b pow (if e < (&0:int) then 0 else num_of_int e)`;;

let gsl_info_b = new_definition `gsl_info_b (q:gsl_info) = FST q`;;

let gsl_data = new_definition `gsl_data (p:gsl_bptr) = FST p`;;
let gsl_off = new_definition `gsl_off (p:gsl_bptr) = FST (SND p)`;;
let gsl_min = new_definition
  `gsl_min (p:gsl_bptr) = FST (SND (SND p))`;;
let gsl_max = new_definition
  `gsl_max (p:gsl_bptr) = FST (SND (SND (SND p)))`;;
let gsl_write = new_definition
  `gsl_write (p:gsl_bptr) = FST (SND (SND (SND (SND p))))`;;
let gsl_zone = new_definition
  `gsl_zone (p:gsl_bptr) = SND (SND (SND (SND (SND p))))`;;

let gsl_pelts = new_definition
  `gsl_pelts p (i:int) =
     let k = if i < (&0:int) then 0 else num_of_int i in
     if k < LENGTH (gsl_data p) then EL k (gsl_data p)
     else (word 0:byte)`;;

let gsl_valid = new_definition
  `gsl_valid p (n:int) <=>
     gsl_i32_bounds n /\ (&0:int) <= n /\
     (&0:int) <= gsl_min p /\ gsl_min p <= gsl_off p /\
     gsl_off p + n <= gsl_max p /\
     gsl_max p <= (&(LENGTH (gsl_data p)):int)`;;
let gsl_access = new_definition
  `gsl_access p (i:int) <=> gsl_min p <= i /\ i < gsl_max p`;;
let gsl_same_frame = new_definition
  `gsl_same_frame newer older <=>
     LENGTH (gsl_data newer) = LENGTH (gsl_data older) /\
     gsl_off newer = gsl_off older /\
     gsl_min newer = gsl_min older /\
     gsl_max newer = gsl_max older /\
     gsl_write newer = gsl_write older /\
     gsl_zone newer = gsl_zone older`;;
let gsl_update = new_definition
  `gsl_update (f:int->A) (i:int) (x:A) =
     \j. if j = i then x else f j`;;

let gsl_svalue_le_sub = new_definition
  `gsl_svalue_le_sub (b:int) (m:int->byte) (lo:int) (hi:int) =
     let n = hi - lo in
     if n <= (&0:int) then (&0:int)
     else isum (0..num_of_int n - 1)
       (\k. b pow k * gsl_u8 (m (lo + &k)))`;;
let gsl_svalue_le = new_definition
  `gsl_svalue_le (b:int) p (n:int) =
     gsl_svalue_le_sub b (gsl_pelts p) (gsl_off p) (gsl_off p + n)`;;
let gsl_in_base = new_definition
  `gsl_in_base (b:int) (m:int->byte) (lo:int) (hi:int) <=>
     !i:int. lo <= i /\ i < hi
             ==> (&0:int) <= gsl_u8 (m i) /\ gsl_u8 (m i) < b`;;
let gsl_frame = new_definition
  `gsl_frame current original (n:int) <=>
     !j:int. j < gsl_off current \/ gsl_off current + n <= j
             ==> gsl_pelts current j = gsl_pelts original j`;;
let gsl_reciprocal = new_definition
  `gsl_reciprocal di d1 <=>
     gsl_u64 di =
       ((gsl_radix * gsl_radix - (&1:int)) div gsl_u64 d1) -
       gsl_radix`;;

let gsl_loop_inv = new_definition
  `gsl_loop_inv base original_sp original_w size current_sp i current_w <=>
     ((&0:int) <= gsl_u64 current_w /\ gsl_u64 current_w < gsl_radix) /\
     ((&0:int) <= gsl_i32 i /\ gsl_i32 i <= gsl_i32 size) /\
     ((&0:int) < gsl_u64 current_w
      ==> (&0:int) <= gsl_i32 i /\ gsl_i32 i < gsl_i32 size) /\
     gsl_in_base base (gsl_pelts current_sp) (gsl_off current_sp)
       (gsl_off current_sp + gsl_i32 i) /\
     (gsl_u64 current_w = (&0:int)
      ==> (&0:int) < gsl_i32 i
      ==> (&0:int) <
          gsl_u8 (gsl_pelts current_sp
            (gsl_off current_sp + gsl_i32 i - (&1:int)))) /\
     gsl_u64 original_w =
       gsl_svalue_le base current_sp (gsl_i32 i) +
       gsl_ipow base (gsl_i32 i) * gsl_u64 current_w /\
     gsl_frame current_sp original_sp (gsl_i32 i)`;;

let gsl_step = new_definition
  `gsl_step base original_sp original_w d1 shift di size
            i current_w current_sp <=>
     gsl_u64_bounds ((&64:int) - gsl_u64 shift) /\
     (!o1:int64.
        gsl_u64 o1 = (&64:int) - gsl_u64 shift
        ==> ((&0:int) <= gsl_u64 o1 /\ gsl_u64 o1 < (&64:int)) /\
            (!h:int64.
               gsl_u64 h =
                 gsl_u64 current_w div
                 gsl_ipow (&2:int) (gsl_u64 o1)
               ==> ((&0:int) <= gsl_u64 shift /\
                    gsl_u64 shift < (&64:int)) /\
                   (!l:int64.
                      gsl_u64 l =
                        (gsl_u64 current_w *
                         gsl_ipow (&2:int) (gsl_u64 shift)) rem
                        gsl_radix
                      ==> (gsl_radix div (&2:int) <= gsl_u64 d1 /\
                           gsl_u64 h < gsl_u64 d1 /\
                           gsl_reciprocal di d1) /\
                          (!q r:int64.
                             gsl_u64 q * gsl_u64 d1 + gsl_u64 r =
                               gsl_u64 l + gsl_radix * gsl_u64 h /\
                             (&0:int) <= gsl_u64 r /\
                             gsl_u64 r < gsl_u64 d1
                             ==> (((&0:int) <= gsl_u64 shift /\
                                   gsl_u64 shift < (&64:int)) /\
                                  gsl_u64 r rem
                                    gsl_ipow (&2:int) (gsl_u64 shift) =
                                    (&0:int)) /\
                                 (!nr:int64.
                                    gsl_u64 r =
                                      gsl_ipow (&2:int) (gsl_u64 shift) *
                                      gsl_u64 nr
                                    ==> (((&0:int) <= gsl_u64 shift /\
                                          gsl_u64 shift < (&64:int)) /\
                                         gsl_u64 r rem
                                           gsl_ipow (&2:int)
                                             (gsl_u64 shift) =
                                           (&0:int)) /\
                                        (!o2:int64.
                                           gsl_u64 r =
                                             gsl_ipow (&2:int)
                                               (gsl_u64 shift) *
                                             gsl_u64 o2
                                           ==> ((&0:int) <= gsl_u64 o2 /\
                                                gsl_u64 o2 <= (&255:int)) /\
                                               (!o3:byte.
                                                  gsl_u8 o3 = gsl_u64 o2
                                                  ==> (gsl_access current_sp
                                                        (gsl_off current_sp +
                                                         gsl_i32 i) /\
                                                       gsl_write current_sp = T) /\
                                                      (!next_sp:gsl_bptr.
                                                         gsl_same_frame
                                                           next_sp current_sp
                                                         ==> gsl_pelts next_sp =
                                                               gsl_update
                                                                 (gsl_pelts
                                                                   current_sp)
                                                                 (gsl_off
                                                                   next_sp +
                                                                  gsl_i32 i)
                                                                 o3 /\
                                                             gsl_pelts next_sp
                                                               (gsl_off next_sp +
                                                                gsl_i32 i) = o3
                                                         ==> gsl_i32_bounds
                                                               (gsl_i32 i +
                                                                (&1:int)) /\
                                                             (!next_i:int32.
                                                                gsl_i32 next_i =
                                                                  gsl_i32 i +
                                                                  (&1:int)
                                                                ==> gsl_u64 q <
                                                                      gsl_u64
                                                                        current_w /\
                                                                    gsl_loop_inv
                                                                      base
                                                                      original_sp
                                                                      original_w
                                                                      size
                                                                      next_sp
                                                                      next_i
                                                                      q)))))))))`;;

let gsl_exit = new_definition
  `gsl_exit base original_sp original_w size i current_sp <=>
     (&0:int) <= gsl_i32 i /\
     (!result:int32.
        gsl_u32 result = gsl_i32 i
        ==> gsl_svalue_le base current_sp (gsl_u32 result) =
              gsl_u64 original_w /\
            ((&0:int) <= gsl_u32 result /\
             gsl_u32 result <= gsl_i32 size) /\
            ((&0:int) < gsl_u32 result
             ==> (&0:int) <
                 gsl_u8 (gsl_pelts current_sp
                   (gsl_off current_sp + gsl_u32 result - (&1:int)))) /\
            gsl_frame current_sp original_sp (gsl_u32 result) /\
            gsl_in_base base (gsl_pelts current_sp) (gsl_off current_sp)
              (gsl_off current_sp + gsl_u32 result))`;;

let statement =
  `!info:gsl_info. !sp:gsl_bptr. !d1 shift di:int64.
   !size:int32. !w:int64.
     (&2:int) <= gsl_info_b info
     ==> gsl_info_b info <= (&256:int)
     ==> gsl_write sp = T
     ==> gsl_radix div (&2:int) <= gsl_u64 d1
     ==> (&0:int) <= gsl_u64 shift
     ==> gsl_u64 shift <= (&63:int)
     ==> gsl_info_b info * gsl_ipow (&2:int) (gsl_u64 shift) =
           gsl_u64 d1
     ==> gsl_reciprocal di d1
     ==> gsl_valid sp (gsl_i32 size)
     ==> (&0:int) < gsl_i32 size
     ==> gsl_u64 w <
           gsl_ipow (gsl_info_b info) (gsl_i32 size)
     ==> gsl_loop_inv (gsl_info_b info) sp w size sp
           (word 0:int32) w /\
         (!i:int32. !current_w:int64. !current_sp:gsl_bptr.
            gsl_same_frame current_sp sp
            ==> gsl_loop_inv (gsl_info_b info) sp w size
                  current_sp i current_w
            ==> if (&0:int) < gsl_u64 current_w then
                  gsl_step (gsl_info_b info) sp w d1 shift di size
                    i current_w current_sp
                else
                  gsl_exit (gsl_info_b info) sp w size i current_sp)`;;
