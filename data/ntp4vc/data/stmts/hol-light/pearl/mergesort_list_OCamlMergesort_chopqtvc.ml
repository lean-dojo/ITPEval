(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_list_OCamlMergesort_chopqtvc: a list-chopping
  verification condition establishing the recursive-call bounds and
  reconstruction of a list from an abstract prefix operation and its
  remaining suffix. This file contains no proof.
*)

let statement =
 `!prefix1:int->A list->A list.
  !n:int.
  !l:A list.
    (!xs:A list. prefix1 (&0:int) xs = [])
    ==>
    (!k:int.
     !x:A.
     !xs:A list.
       (&0:int) < k
       ==>
       prefix1 k (CONS x xs) =
       CONS x (prefix1 (k - (&1:int)) xs))
    ==>
    (&0:int) <= n
    ==>
    n <= (&(LENGTH l):int)
    ==>
    (~(n = (&0:int))
     ==>
     ~(l = []) /\
     (let o1 = n - (&1:int) in
      (((&0:int) <= n /\ o1 < n) /\
       (&0:int) <= o1 /\
       o1 <= (&(LENGTH (TL l)):int)))) /\
    (!result:A list.
       (if n = (&0:int) then
          result = l
        else
          ~(l = []) /\
          TL l =
          APPEND (prefix1 (n - (&1:int)) (TL l)) result)
       ==>
       l = APPEND (prefix1 n l) result)`;;
