(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_reciprocal_word_3by2qtvc: the verification
  condition for computing a reciprocal approximation for a normalized
  two-limb 64-bit divisor, including the carry, borrow, product, and final
  quotient-correction branches. This file contains no proof.
*)

needs "Library/words.ml";;

let statement =
  `let radix = (&18446744073709551616:int) in
   let u64 = \x:int64. (&(val x):int) in
   let uint64_in_bounds =
     \z:int.
       (&0:int) <= z /\ z <= (&18446744073709551615:int) in
   let reciprocal =
     \(v:int64) (d:int64).
       u64 v =
         (radix * radix - (&1:int)) div u64 d - radix in
   let reciprocal_3by2 =
     \(v:int64) (dh:int64) (dl:int64).
       u64 v =
         (radix * radix * radix - (&1:int)) div
           (u64 dl + radix * u64 dh) -
         radix in
   let flag_relation =
     \(x:int64) (tl:int64) (dh:int64) (dl:int64) (flag:bool).
       (if u64 dh < u64 x then
          flag = T
        else
          ?equal_flag:bool.
            ((u64 x = u64 dh ==> equal_flag = T) /\
             (equal_flag = T ==> x = dh)) /\
            (if equal_flag = T then
               flag = (if u64 dl <= u64 tl then T else F)
             else
               flag = F)) in
   let corrected_reciprocal =
     \(q:int64) (flag:bool) (dh:int64) (dl:int64).
       (if flag = T then
          uint64_in_bounds (u64 q - (&1:int)) /\
          (!q1:int64.
             u64 q1 = u64 q - (&1:int)
             ==>
             uint64_in_bounds (u64 q1 - (&1:int)) /\
             (!q2:int64.
                u64 q2 = u64 q1 - (&1:int)
                ==>
                reciprocal_3by2 q2 dh dl))
        else
          uint64_in_bounds (u64 q - (&1:int)) /\
          (!q1:int64.
             u64 q1 = u64 q - (&1:int)
             ==>
             reciprocal_3by2 q1 dh dl)) in
   let finish_correction =
     \(q:int64) (x:int64) (tl:int64) (th:int64)
      (dh:int64) (dl:int64).
       (if u64 x < u64 th then
          !flag:bool.
            flag_relation x tl dh dl flag
            ==>
            corrected_reciprocal q flag dh dl
        else
          reciprocal_3by2 q dh dl) in
   !dh:int64. !dl:int64.
     radix div (&2:int) <= u64 dh
     ==>
     radix div (&2:int) <= u64 dh /\
     (!o1:int64.
        reciprocal o1 dh
        ==>
        (!o2:int64.
           u64 o2 = (u64 dh * u64 o1) rem radix
           ==>
           (!o3:int64.
              u64 o3 = (u64 o2 + u64 dl) rem radix
              ==>
              (if u64 o3 < u64 dl then
                 (if u64 dh <= u64 o3 then
                    uint64_in_bounds (u64 o1 - (&1:int)) /\
                    (!o4:int64.
                       u64 o4 = u64 o1 - (&1:int)
                       ==>
                       uint64_in_bounds (u64 o3 - u64 dh) /\
                       (!o5:int64.
                          u64 o5 = u64 o3 - u64 dh
                          ==>
                          uint64_in_bounds (u64 o4 - (&1:int)) /\
                          (!o6:int64.
                             u64 o6 = u64 o4 - (&1:int)
                             ==>
                             (!o7:int64.
                                u64 o7 =
                                  (u64 o5 - u64 dh) rem radix
                                ==>
                                (!tl:int64. !th:int64.
                                   u64 tl + radix * u64 th =
                                     u64 o6 * u64 dl
                                   ==>
                                   (!o8:int64.
                                      u64 o8 =
                                        (u64 o7 + u64 th) rem radix
                                      ==>
                                      finish_correction
                                        o6 o8 tl th dh dl))))))
                  else
                    uint64_in_bounds (u64 o1 - (&1:int)) /\
                    (!o4:int64.
                       u64 o4 = u64 o1 - (&1:int)
                       ==>
                       (!o5:int64.
                          u64 o5 =
                            (u64 o3 - u64 dh) rem radix
                          ==>
                          (!tl:int64. !th:int64.
                             u64 tl + radix * u64 th =
                               u64 o4 * u64 dl
                             ==>
                             (!o6:int64.
                                u64 o6 =
                                  (u64 o5 + u64 th) rem radix
                                ==>
                                finish_correction
                                  o4 o6 tl th dh dl)))))
               else
                 (!tl:int64. !th:int64.
                    u64 tl + radix * u64 th =
                      u64 o1 * u64 dl
                    ==>
                    (!o4:int64.
                       u64 o4 =
                         (u64 o3 + u64 th) rem radix
                       ==>
                       finish_correction
                         o1 o4 tl th dh dl))))))`;;
