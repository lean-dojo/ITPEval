(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/word_common_factor_Top_powerqtvc: the recursive integer-power
  termination condition that subtracting one from a nonzero nonnegative
  exponent yields a nonnegative smaller exponent. This file contains no proof.
*)

let statement =
 `!n:int.
    (&0:int) <= n
    ==>
    ~(n = (&0:int))
    ==>
    let o1 = n - (&1:int) in
    (((&0:int) <= n /\ o1 < n) /\ (&0:int) <= o1)`;;
