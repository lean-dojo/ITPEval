(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/base_info_BaseInfo_wmpn_get_base_infoqtvc: the
  verification condition for computing a multiprecision base record by
  repeatedly multiplying a 64-bit power while it remains below the quotient
  of the maximum limb by the base. This file contains no proof.
*)

needs "Library/words.ml";;

let statement =
 `let cdiv =
    \(n:int) (d:int).
      if (&0:int) <= n
      then if (&0:int) <= d then n div d else --(n div --d)
      else if (&0:int) <= d then --(--n div d) else --n div --d in
  let uint64_in_bounds =
    \z:int.
      (&0:int) <= z /\ z <= (&18446744073709551615:int) in
  let uint32_in_bounds =
    \z:int.
      (&0:int) <= z /\ z <= (&4294967295:int) in
  let base_info_invariant =
    \(r:(int#(int32#int64))).
      (&2:int) <= FST r /\
      FST r <= (&256:int) /\
      (&(val (SND (SND r))):int) <
        (&18446744073709551615:int) + (&1:int) /\
      (&18446744073709551615:int) + (&1:int) <=
        (&(val (SND (SND r))):int) * FST r /\
      (&7:int) <= (&(val (FST (SND r))):int) /\
      (&(val (FST (SND r))):int) <= (&63:int) /\
      (&(val (SND (SND r))):int) =
        FST r pow (val (FST (SND r))) in
  !b1:int64.
    (&2:int) <= (&(val b1):int)
    ==>
    (&(val b1):int) <= (&256:int)
    ==>
    ~((&(val b1):int) = (&0:int)) /\
    uint64_in_bounds
      (cdiv (&18446744073709551615:int) (&(val b1):int)) /\
    (!m:int64.
       (&(val m):int) =
         cdiv (&18446744073709551615:int) (&(val b1):int)
       ==>
       ((&(val b1):int) pow 1 = (&(val b1):int) /\
        (&1:int) <= (&1:int) /\
        (&1:int) <= (&64:int)) /\
       (!exp1:int32. !p:int64.
          (&(val b1):int) pow (val exp1) = (&(val p):int) /\
          (&1:int) <= (&(val exp1):int) /\
          (&(val exp1):int) <= (&64:int)
          ==>
          if (&(val p):int) <= (&(val m):int) then
            uint64_in_bounds
              ((&(val p):int) * (&(val b1):int)) /\
            (!o1:int64.
               (&(val o1):int) =
                 (&(val p):int) * (&(val b1):int)
               ==>
               uint32_in_bounds
                 ((&(val exp1):int) + (&1:int)) /\
               (!o2:int32.
                  (&(val o2):int) =
                    (&(val exp1):int) + (&1:int)
                  ==>
                  ((&0:int) <=
                     (&(val m):int) - (&(val p):int) /\
                   (&(val m):int) - (&(val o1):int) <
                     (&(val m):int) - (&(val p):int)) /\
                  (&(val b1):int) pow (val o2) =
                    (&(val o1):int) /\
                  (&1:int) <= (&(val o2):int) /\
                  (&(val o2):int) <= (&64:int)))
          else
            let o1 = (&(val b1):int) in
            ((&2:int) <= o1 /\ o1 <= (&256:int)) /\
            ((&(val p):int) <
               (&18446744073709551615:int) + (&1:int) /\
             (&18446744073709551615:int) + (&1:int) <=
               (&(val p):int) * o1) /\
            ((&7:int) <= (&(val exp1):int) /\
             (&(val exp1):int) <= (&63:int)) /\
            (&(val p):int) = o1 pow (val exp1) /\
            (!result:(int#(int32#int64)).
               base_info_invariant result
               ==>
               FST result = o1 /\
               FST (SND result) = exp1 /\
               SND (SND result) = p
               ==>
               FST result = (&(val b1):int))))`;;
