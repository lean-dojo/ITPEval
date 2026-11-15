(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_invert_limbqtvc: the verification condition
  that the complement and quotient limbs for a normalized unsigned 64-bit
  divisor satisfy the prescribed reciprocal equation. This file contains no
  proof.
*)

let statement =
  `let radix = 18446744073709551616 in
   let word64 = \x:num. x < radix in
   let reciprocal =
     \v d:num.
       v = (radix * radix - 1) DIV d - radix in
   !d:num.
     word64 d /\
     radix DIV 2 <= d
     ==>
     let o1 = 18446744073709551615 in
     word64 (o1 - d) /\
     (!o2:num.
        word64 o2
        ==>
        o2 = o1 - d
        ==>
        o2 < d /\
        (!v:num.
           word64 v
           ==>
           v = (o1 + radix * o2) DIV d
           ==>
           reciprocal v d))`;;
