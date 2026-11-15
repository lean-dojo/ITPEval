(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/power_FastExponentiation_fast_exp_imperativeqtvc: the imperative
  fast-exponentiation verification condition, including initialization,
  loop-invariant preservation, descent, and final correctness for a
  nonnegative integer exponent. This file contains no proof.
*)

let statement =
 `let cdiv =
    \(n:int) (d:int).
      if (&0:int) <= n
      then if (&0:int) <= d then n div d else --(n div --d)
      else if (&0:int) <= d then --(--n div d) else --n div --d in
  let cmod =
    \(n:int) (d:int). n - d * cdiv n d in
  !n x:int.
    (&0:int) <= n
    ==>
    (&0:int) <= n /\
    (&1:int) * x pow (num_of_int n) = x pow (num_of_int n) /\
    (!e p r:int.
       (&0:int) <= e /\
       r * p pow (num_of_int e) = x pow (num_of_int n)
       ==>
       if (&0:int) < e then
         ~((&2:int) = (&0:int)) /\
         (let half = cdiv e (&2:int) in
          if cmod e (&2:int) = (&1:int) then
            ~((&2:int) = (&0:int)) /\
            ((&0:int) <= e /\ half < e) /\
            (&0:int) <= half /\
            r * p * (p * p) pow (num_of_int half) =
              x pow (num_of_int n)
          else
            ~((&2:int) = (&0:int)) /\
            ((&0:int) <= e /\ half < e) /\
            (&0:int) <= half /\
            r * (p * p) pow (num_of_int half) =
              x pow (num_of_int n))
       else
         r = x pow (num_of_int n))`;;
