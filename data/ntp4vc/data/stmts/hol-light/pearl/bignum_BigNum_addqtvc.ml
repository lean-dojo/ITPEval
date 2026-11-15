(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bignum_BigNum_addqtvc:
  a big-integer addition verification condition stating validity and numeric
  value preservation for the sum of two valid base-digit lists. This file
  contains no proof.
*)

let ntp4vc_bignum_add_value = new_recursive_definition list_RECURSION
  `(ntp4vc_bignum_add_value (base:int) ([]:int list) = (&0:int)) /\
   (!d r.
      ntp4vc_bignum_add_value base (CONS d r) =
      d + base * ntp4vc_bignum_add_value base r)`;;

let ntp4vc_bignum_add_valid = new_recursive_definition list_RECURSION
  `(ntp4vc_bignum_add_valid (base:int) ([]:int list) = T) /\
   (!d r.
      ntp4vc_bignum_add_valid base (CONS d r) =
      if r = [] then
        (&0:int) < d /\ d < base
      else
        ((&0:int) <= d /\ d < base) /\
        ntp4vc_bignum_add_valid base r)`;;

let statement =
  `!base:int.
     (&1:int) < base ==>
     !n1 n2:int list.
       ntp4vc_bignum_add_valid base n1 ==>
       ntp4vc_bignum_add_valid base n2 ==>
       ntp4vc_bignum_add_valid base n1 /\
       ntp4vc_bignum_add_valid base n2 /\
       (&0:int) <= (&0:int) /\
       (&0:int) <= (&1:int) /\
       (!result:int list.
          ntp4vc_bignum_add_valid base result /\
          ntp4vc_bignum_add_value base result =
            ntp4vc_bignum_add_value base n1 +
            ntp4vc_bignum_add_value base n2 + (&0:int)
          ==>
          ntp4vc_bignum_add_valid base result /\
          ntp4vc_bignum_add_value base result =
            ntp4vc_bignum_add_value base n1 +
            ntp4vc_bignum_add_value base n2)`;;
