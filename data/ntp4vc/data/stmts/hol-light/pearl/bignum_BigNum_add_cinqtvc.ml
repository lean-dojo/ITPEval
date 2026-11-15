(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bignum_BigNum_add_cinqtvc:
  a big-integer addition-with-carry verification condition relating valid
  base-digit lists to their positional integer values. This file contains
  no proof.
*)

let statement =
 `!base:int.
  !value:int list->int.
  !valid:int list->bool.
  !n1 n2:int list.
  !cin:int.
    (&1:int) < base ==>
    value ([]:int list) = (&0:int) ==>
    (!d r.
       value (CONS d r) = d + base * value r) ==>
    valid ([]:int list) ==>
    (!d r.
       (valid (CONS d r) <=>
        if r = [] then
          (&0:int) < d /\ d < base
        else
          ((&0:int) <= d /\ d < base) /\ valid r)) ==>
    valid n1 ==>
    valid n2 ==>
    (&0:int) <= cin ==>
    cin <= (&1:int) ==>
    ((if n2 = [] then
        if n1 = [] then
          valid n2 /\ (&0:int) <= cin /\ cin < base
        else
          valid n1 /\ (&0:int) <= cin /\ cin < base
      else
        if n1 = [] then
          valid n2 /\ (&0:int) <= cin /\ cin < base
        else
          if cin + HD n1 + HD n2 < base then
            TL n1 = TL n1 /\
            valid (TL n1) /\
            valid (TL n2) /\
            (&0:int) <= (&0:int) /\
            (&0:int) <= (&1:int)
          else
            TL n1 = TL n1 /\
            valid (TL n1) /\
            valid (TL n2) /\
            (&0:int) <= (&1:int) /\
            (&1:int) <= (&1:int)) /\
     (!result:int list.
        (if n2 = [] then
           if n1 = [] then
             valid result /\
             value result = value n2 + cin
           else
             valid result /\
             value result = value n1 + cin
         else
           if n1 = [] then
             valid result /\
             value result = value n2 + cin
           else
             let d = cin + HD n1 + HD n2 in
             if d < base then
               ?o1:int list.
                 (valid o1 /\
                  value o1 =
                    value (TL n1) + value (TL n2) + (&0:int)) /\
                 result = CONS d o1
             else
               ?o1:int list.
                 (valid o1 /\
                  value o1 =
                    value (TL n1) + value (TL n2) + (&1:int)) /\
                 result = CONS (d - base) o1)
        ==>
        valid result /\
        value result = value n1 + value n2 + cin))`;;
