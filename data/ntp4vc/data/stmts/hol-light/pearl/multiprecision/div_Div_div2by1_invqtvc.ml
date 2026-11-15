(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_div2by1_invqtvc: the verification condition
  for reciprocal-based division of a two-limb unsigned integer by a
  normalized 64-bit divisor, including carry reconstruction and the two
  quotient-remainder correction branches. This file contains no proof.
*)

needs "Library/words.ml";;

let statement =
  `let radix = (&18446744073709551616:int) in
   let uint64_in_bounds =
     \z:int.
       (&0:int) <= z /\ z <= (&18446744073709551615:int) in
   let reciprocal =
     \(v:int64) (d:int64).
       (&(val v):int) =
         (radix * radix - (&1:int)) div (&(val d):int) - radix in
   !d:int64. !uh:int64. !v:int64.
   !l:int64. !h:int64. !ul:int64.
     radix div (&2:int) <= (&(val d):int)
     ==>
     (&(val uh):int) < (&(val d):int)
     ==>
     reciprocal v d
     ==>
     (&(val l):int) + radix * (&(val h):int) =
       (&(val v):int) * (&(val uh):int)
     ==>
     (&0:int) <= (&0:int) /\
     (&0:int) <= (&1:int) /\
     (!sl:int64. !c:int64.
        (&(val sl):int) + radix * (&(val c):int) =
          (&(val l):int) + (&(val ul):int) + (&0:int) /\
        (&0:int) <= (&(val c):int) /\
        (&(val c):int) <= (&1:int)
        ==>
        ((&0:int) <= (&(val c):int) /\
         (&(val c):int) <= (&1:int)) /\
        (!sh:int64. !c2:int64.
           (&(val sh):int) + radix * (&(val c2):int) =
             (&(val uh):int) + (&(val h):int) + (&(val c):int) /\
           (&0:int) <= (&(val c2):int) /\
           (&(val c2):int) <= (&1:int)
           ==>
           (!o1:int64.
              (&(val o1):int) =
                ((&(val sh):int) + (&1:int)) rem radix
              ==>
              (!p:int64.
                 (&(val p):int) =
                   ((&(val o1):int) * (&(val d):int)) rem radix
                 ==>
                 (!o2:int64.
                    (&(val o2):int) =
                      ((&(val ul):int) - (&(val p):int)) rem radix
                    ==>
                    if (&(val sl):int) < (&(val o2):int) then
                      (!o3:int64.
                         (&(val o3):int) =
                           ((&(val o1):int) - (&1:int)) rem radix
                         ==>
                         (!o4:int64.
                            (&(val o4):int) =
                              ((&(val o2):int) + (&(val d):int)) rem
                              radix
                            ==>
                            if (&(val d):int) <= (&(val o4):int) then
                              uint64_in_bounds
                                ((&(val o3):int) + (&1:int)) /\
                              (!o5:int64.
                                 (&(val o5):int) =
                                   (&(val o3):int) + (&1:int)
                                 ==>
                                 uint64_in_bounds
                                   ((&(val o4):int) - (&(val d):int)) /\
                                 (!o6:int64.
                                    (&(val o6):int) =
                                      (&(val o4):int) - (&(val d):int)
                                    ==>
                                    (&(val o5):int) * (&(val d):int) +
                                      (&(val o6):int) =
                                      (&(val ul):int) +
                                      radix * (&(val uh):int) /\
                                    (&0:int) <= (&(val o6):int) /\
                                    (&(val o6):int) < (&(val d):int)))
                            else
                              (&(val o3):int) * (&(val d):int) +
                                (&(val o4):int) =
                                (&(val ul):int) +
                                radix * (&(val uh):int) /\
                              (&0:int) <= (&(val o4):int) /\
                              (&(val o4):int) < (&(val d):int)))
                    else if (&(val d):int) <= (&(val o2):int) then
                      uint64_in_bounds
                        ((&(val o1):int) + (&1:int)) /\
                      (!o3:int64.
                         (&(val o3):int) =
                           (&(val o1):int) + (&1:int)
                         ==>
                         uint64_in_bounds
                           ((&(val o2):int) - (&(val d):int)) /\
                         (!o4:int64.
                            (&(val o4):int) =
                              (&(val o2):int) - (&(val d):int)
                            ==>
                            (&(val o3):int) * (&(val d):int) +
                              (&(val o4):int) =
                              (&(val ul):int) +
                              radix * (&(val uh):int) /\
                            (&0:int) <= (&(val o4):int) /\
                            (&(val o4):int) < (&(val d):int)))
                    else
                      (&(val o1):int) * (&(val d):int) +
                        (&(val o2):int) =
                        (&(val ul):int) + radix * (&(val uh):int) /\
                       (&0:int) <= (&(val o2):int) /\
                       (&(val o2):int) < (&(val d):int))))))`;;
