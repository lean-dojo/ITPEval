(*
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/div_Div_div3by2_invqtvc: the verification condition
  for reciprocal-based division of a three-limb unsigned integer by a
  normalized two-limb 64-bit divisor, including quotient corrections and
  the final two-limb remainder bound. This file contains no proof.
*)

needs "Library/words.ml";;

let statement =
  `let radix = (&18446744073709551616:int) in
   let u64 = \x:int64. (&(val x):int) in
   let carry =
     \x:int64. (&0:int) <= u64 x /\ u64 x <= (&1:int) in
   let vc_zero_one_bounds =
     ((&0:int) <= (&0:int) /\ (&0:int) <= (&1:int)) in
   let reciprocal_3by2 =
     \(v:int64) (dh:int64) (dl:int64).
       u64 v =
         (radix * radix * radix - (&1:int)) div
           (u64 dl + radix * u64 dh) -
         radix in
   let result =
     \(q:int64) (rl:int64) (rh:int64)
      (dl:int64) (dh:int64) (ul:int64) (um:int64) (uh:int64).
       u64 q * u64 dl +
           radix * u64 q * u64 dh +
           u64 rl + radix * u64 rh =
         u64 ul + radix * u64 um + radix * radix * u64 uh /\
       (&0:int) <= u64 rl + radix * u64 rh /\
       u64 rl + radix * u64 rh < u64 dl + radix * u64 dh in
   !dh:int64. !v:int64. !dl:int64. !um:int64.
   !uh:int64. !l:int64. !h:int64. !ul:int64.
     radix div (&2:int) <= u64 dh
     ==>
     reciprocal_3by2 v dh dl
     ==>
     u64 um + radix * u64 uh < u64 dl + radix * u64 dh
     ==>
     u64 l + radix * u64 h = u64 v * u64 uh
     ==>
     (&0:int) <= (&0:int) /\
     (&0:int) <= (&1:int) /\
     (!sl:int64. !c:int64.
        u64 sl + radix * u64 c = u64 um + u64 l + (&0:int) /\
        carry c
        ==>
        carry c /\
        (!sh:int64. !c2:int64.
           u64 sh + radix * u64 c2 = u64 uh + u64 h + u64 c /\
           carry c2
           ==>
           (!o1:int64.
              u64 o1 = (u64 sh + (&1:int)) rem radix
              ==>
              (!p:int64.
                 u64 p = (u64 dh * u64 sh) rem radix
                 ==>
                 (!o2:int64.
                    u64 o2 = (u64 um - u64 p) rem radix
                    ==>
                    ~(radix = (&0:int)) /\
                    (!tl:int64. !th:int64.
                       u64 tl + radix * u64 th = u64 sh * u64 dl
                       ==>
                       vc_zero_one_bounds /\
                       (!il:int64. !b:int64.
                          u64 il - radix * u64 b =
                            u64 ul - u64 tl - (&0:int) /\
                          carry b
                          ==>
                          carry b /\
                          (!ih:int64. !bprime:int64.
                             u64 ih - radix * u64 bprime =
                               u64 o2 - u64 th - u64 b /\
                             carry bprime
                             ==>
                             vc_zero_one_bounds /\
                             (!bl:int64. !b2:int64.
                                u64 bl - radix * u64 b2 =
                                  u64 il - u64 dl - (&0:int) /\
                                carry b2
                                ==>
                                carry b2 /\
                                (!bh:int64. !b2prime:int64.
                                   u64 bh - radix * u64 b2prime =
                                     u64 ih - u64 dh - u64 b2 /\
                                   carry b2prime
                                   ==>
                                   if u64 sl <= u64 bh then
                                     (!o3:int64.
                                        u64 o3 =
                                          (u64 o1 - (&1:int)) rem radix
                                        ==>
                                        vc_zero_one_bounds /\
                                        (!rl:int64. !c1:int64.
                                           u64 rl + radix * u64 c1 =
                                             u64 bl + u64 dl + (&0:int) /\
                                           carry c1
                                           ==>
                                           carry c1 /\
                                           (!rh:int64. !c1prime:int64.
                                              u64 rh +
                                                  radix * u64 c1prime =
                                                u64 bh + u64 dh + u64 c1 /\
                                              carry c1prime
                                              ==>
                                              (!o4:bool.
                                                 (if u64 dh < u64 rh then
                                                    o4 = T
                                                  else
                                                    ?o5:bool.
                                                      ((u64 rh = u64 dh
                                                        ==> o5 = T) /\
                                                       (o5 = T
                                                        ==> rh = dh)) /\
                                                      o4 =
                                                        (if o5 = T then
                                                           if u64 dl <= u64 rl
                                                           then T
                                                           else F
                                                         else F))
                                                 ==>
                                                 if o4 = T then
                                                   vc_zero_one_bounds /\
                                                   (!bl1:int64. !b1:int64.
                                                      u64 bl1 -
                                                          radix * u64 b1 =
                                                        u64 rl - u64 dl -
                                                          (&0:int) /\
                                                      carry b1
                                                      ==>
                                                      carry b1 /\
                                                      (!bh1:int64.
                                                       !b1prime:int64.
                                                         u64 bh1 -
                                                             radix *
                                                               u64 b1prime =
                                                           u64 rh - u64 dh -
                                                             u64 b1 /\
                                                         carry b1prime
                                                         ==>
                                                         (!o5:int64.
                                                            u64 o5 =
                                                              (u64 o3 +
                                                               (&1:int)) rem
                                                                radix
                                                            ==>
                                                            result
                                                              o5 bl1 bh1
                                                              dl dh ul um uh)))
                                                   else
                                                     result
                                                       o3 rl rh
                                                       dl dh ul um uh))))
                                   else
                                     (!o3:bool.
                                        (if u64 dh < u64 bh then
                                           o3 = T
                                         else
                                           ?o4:bool.
                                             ((u64 bh = u64 dh
                                               ==> o4 = T) /\
                                              (o4 = T ==> bh = dh)) /\
                                             o3 =
                                               (if o4 = T then
                                                  if u64 dl <= u64 bl
                                                  then T
                                                  else F
                                                else F))
                                        ==>
                                        if o3 = T then
                                          vc_zero_one_bounds /\
                                          (!bl1:int64. !b3:int64.
                                             u64 bl1 - radix * u64 b3 =
                                               u64 bl - u64 dl - (&0:int) /\
                                             carry b3
                                             ==>
                                             carry b3 /\
                                             (!bh1:int64. !b3prime:int64.
                                                u64 bh1 -
                                                    radix * u64 b3prime =
                                                  u64 bh - u64 dh - u64 b3 /\
                                                carry b3prime
                                                ==>
                                                (!o4:int64.
                                                   u64 o4 =
                                                     (u64 o1 + (&1:int)) rem
                                                       radix
                                                   ==>
                                                   result
                                                     o4 bl1 bh1
                                                     dl dh ul um uh)))
                                        else
                                          result
                                            o1 bl bh dl dh ul um uh)))))))))))`;;
