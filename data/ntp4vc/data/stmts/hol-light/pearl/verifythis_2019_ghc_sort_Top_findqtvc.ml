(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_findqtvc: the recursive verification
  condition for finding an integer value in a nonempty half-open sequence
  interval with a positive occurrence count. This file contains no proof.
*)

let ntp4vc_find_drop =
  new_recursive_definition num_RECURSION
   `(!xs:A list. ntp4vc_find_drop 0 xs = xs) /\
    (!n:num.
     !xs:A list.
       ntp4vc_find_drop (SUC n) xs =
       if xs = [] then []
       else ntp4vc_find_drop n (TL xs))`;;

let ntp4vc_find_take =
  new_recursive_definition num_RECURSION
   `(!xs:A list. ntp4vc_find_take 0 xs = []) /\
    (!n:num.
     !xs:A list.
       ntp4vc_find_take (SUC n) xs =
       if xs = [] then []
       else CONS (HD xs) (ntp4vc_find_take n (TL xs)))`;;

let statement =
 `let index =
    \(i:int). if i < (&0:int) then 0 else num_of_int i in
  let nth =
    \(xs:int list) (i:int).
      if index i < LENGTH xs then EL (index i) xs else (&0:int) in
  let interval =
    \(xs:int list) (lower:int) (upper:int).
      ntp4vc_find_take
        (index (upper - lower))
        (ntp4vc_find_drop (index lower) xs) in
  let occurrences =
    \(value:int) (xs:int list) (lower:int) (upper:int).
      LENGTH
        (FILTER
          (\x:int. x = value)
          (interval xs lower upper)) in
  !s e:int. !seq1:int list. !v:int.
    (&0:int) <= s
    ==> s < e
    ==> e <= &(LENGTH seq1)
    ==> (&1:int) <= &(occurrences v seq1 s e)
    ==>
    let o1 = nth seq1 s in
    (~(o1 = v)
     ==>
     let o2 = s + (&1:int) in
     ((&0:int) <= e - s /\ e - o2 < e - s) /\
     ((&0:int) <= o2 /\
      o2 < e /\
      e <= &(LENGTH seq1)) /\
     (&1:int) <= &(occurrences v seq1 o2 e)) /\
    (!result:int.
       (if o1 = v then
          result = s
        else
          (s + (&1:int) <= result /\ result < e) /\
          nth seq1 result = v)
       ==>
       (s <= result /\ result < e) /\
       nth seq1 result = v)`;;
