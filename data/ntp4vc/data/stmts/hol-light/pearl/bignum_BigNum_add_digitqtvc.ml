(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bignum_BigNum_add_digitqtvc:
  a big-integer verification condition for adding one base digit to a valid
  positional integer-digit list, including the carry case and preservation of
  validity and numeric value. This file contains no proof.
*)

let ntp4vc_bignum_value = new_recursive_definition list_RECURSION
  `(ntp4vc_bignum_value (base:int) ([]:int list) = (&0:int)) /\
   (!d r.
      ntp4vc_bignum_value base (CONS d r) =
      d + base * ntp4vc_bignum_value base r)`;;

let ntp4vc_bignum_valid = new_recursive_definition list_RECURSION
  `(ntp4vc_bignum_valid (base:int) ([]:int list) = T) /\
   (!d r.
      ntp4vc_bignum_valid base (CONS d r) =
      if r = [] then
        (&0:int) < d /\ d < base
      else
        ((&0:int) <= d /\ d < base) /\ ntp4vc_bignum_valid base r)`;;

let statement =
  `!base:int.
     (&1:int) < base ==>
     !n:int list. !d:int.
       ntp4vc_bignum_valid base n ==>
       (&0:int) <= d ==>
       d < base ==>
       ((if n = [] then
           T
         else
           ~(d + HD n < base) ==>
           TL n = TL n /\
           ntp4vc_bignum_valid base (TL n) /\
           (&0:int) <= (&1:int) /\
           (&1:int) < base) /\
        (!result:int list.
           (if n = [] then
              if d = (&0:int) then
                result = []
              else
                result = CONS d []
            else
              if d + HD n < base then
                result = CONS (d + HD n) (TL n)
              else
                ?o1:int list.
                  (ntp4vc_bignum_valid base o1 /\
                   ntp4vc_bignum_value base o1 =
                     ntp4vc_bignum_value base (TL n) + (&1:int)) /\
                  result = CONS (d + HD n - base) o1)
           ==>
           ntp4vc_bignum_valid base result /\
           ntp4vc_bignum_value base result =
             ntp4vc_bignum_value base n + d))`;;
