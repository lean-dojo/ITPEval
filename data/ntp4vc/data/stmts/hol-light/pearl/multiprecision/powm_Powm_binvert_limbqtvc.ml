(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_binvert_limbqtvc: the verification condition
  for Newton-style inversion of an odd unsigned 64-bit limb, from an
  eight-bit inverse through three precision-doubling steps. This file
  contains no proof.
*)

needs "Library/words.ml";;

let statement =
  `let radix = (&18446744073709551616:int) in
   let u64 = \(x:int64). (&(val x):int) in
   let uint64_in_bounds =
     \z:int.
       (&0:int) <= z /\ z <= (&18446744073709551615:int) in
   let int_power =
     \(base:int) (exponent:int). base pow (num_of_int exponent) in
   !n:int64.
     ODD (val n)
     ==>
     (!n1:int. !inv_value:int. !prec:int.
        (((&0:int) <= n1 /\ (&0:int) <= inv_value) /\
         (inv_value * n1) rem (int_power (&2:int) prec) = (&1:int) /\
         (&0:int) <= (&2:int) * prec /\
         (&2:int) * prec <= (&64:int))
        ==>
        ((((&2:int) * inv_value -
           inv_value * (inv_value * n1)) rem radix) * n1)
          rem (int_power (&2:int) ((&2:int) * prec)) =
        (&1:int)) /\
     ~((&2:int) = (&0:int)) /\
     uint64_in_bounds (u64 n div (&2:int)) /\
     (!o1:int64.
        u64 o1 = u64 n div (&2:int)
        ==>
        (~((&128:int) = (&0:int)) /\
         uint64_in_bounds (u64 o1 rem (&128:int))) /\
        (!h:int64.
           u64 h = u64 o1 rem (&128:int)
           ==>
           ((&0:int) <= u64 h /\ u64 h < (&128:int)) /\
           (!o2:int64.
              (((&0:int) <= u64 o2 /\ u64 o2 < (&256:int)) /\
               (u64 o2 * ((&2:int) * u64 h + (&1:int)))
                 rem ((&2:int) pow 8) =
               (&1:int))
              ==>
              (!o3:int64.
                 u64 o3 = (u64 o2 * u64 n) rem radix
                 ==>
                 (!o4:int64.
                    u64 o4 = (u64 o2 * u64 o3) rem radix
                    ==>
                    (!o5:int64.
                       u64 o5 = ((&2:int) * u64 o2) rem radix
                       ==>
                       (!o6:int64.
                          u64 o6 = (u64 o5 - u64 o4) rem radix
                          ==>
                          (!o7:int64.
                             u64 o7 = (u64 o6 * u64 n) rem radix
                             ==>
                             (!o8:int64.
                                u64 o8 =
                                  (u64 o6 * u64 o7) rem radix
                                ==>
                                (!o9:int64.
                                   u64 o9 =
                                     ((&2:int) * u64 o6) rem radix
                                   ==>
                                   (!o10:int64.
                                      u64 o10 =
                                        (u64 o9 - u64 o8) rem radix
                                      ==>
                                      (!o11:int64.
                                         u64 o11 =
                                           (u64 o10 * u64 n) rem radix
                                         ==>
                                         (!o12:int64.
                                            u64 o12 =
                                              (u64 o10 * u64 o11)
                                                rem radix
                                            ==>
                                            (!o13:int64.
                                               u64 o13 =
                                                 ((&2:int) * u64 o10)
                                                   rem radix
                                               ==>
                                               (!o14:int64.
                                                  u64 o14 =
                                                    (u64 o13 - u64 o12)
                                                      rem radix
                                                  ==>
                                                  (u64 o14 * u64 n)
                                                    rem radix =
                                                  (&1:int))))))))))))))))`;;
