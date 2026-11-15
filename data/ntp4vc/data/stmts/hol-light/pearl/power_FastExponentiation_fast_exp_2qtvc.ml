(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/power_FastExponentiation_fast_exp_2qtvc: the accumulator-based fast
  exponentiation verification condition for recursive-call descent and
  preservation of the integer power result. This file contains no proof.
*)

let statement =
 `!n acc x:int.
    (&0:int) <= n
    ==>
    ((~(n = (&0:int))
      ==>
      ~((&2:int) = (&0:int)) /\
      (if n rem (&2:int) = (&0:int) then
         ~((&2:int) = (&0:int)) /\
         (let o1 = n div (&2:int) in
          (((&0:int) <= n /\ o1 < n) /\ (&0:int) <= o1))
       else
         let o1 = n - (&1:int) in
         (((&0:int) <= n /\ o1 < n) /\ (&0:int) <= o1)))
     /\
     (!result:int.
        (if n = (&0:int) then
           result = acc
         else if n rem (&2:int) = (&0:int) then
           result =
             (x * x) pow (num_of_int (n div (&2:int))) * acc
         else
           result =
             x pow (num_of_int (n - (&1:int))) * (x * acc))
        ==>
        result = x pow (num_of_int n) * acc))`;;
