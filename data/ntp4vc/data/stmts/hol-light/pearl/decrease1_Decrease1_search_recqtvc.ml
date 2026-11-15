(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/decrease1_Decrease1_search_recqtvc: an integer-list recursive search
  verification condition preserving a decrease-by-at-most-one property and
  specifying the first zero at or after the search index. This file contains
  no proof.
*)

let statement =
 `let nth_i =
    \(a:int list) (r:int).
      if r < (&0:int) then
        if a = [] then (&0:int) else EL 0 a
      else if num_of_int r < LENGTH a then EL (num_of_int r) a
      else (&0:int) in
  let decrease1 =
    \(a:int list).
      !r:int.
        (&0:int) <= r /\ r < &(LENGTH a) - (&1:int)
        ==> nth_i a r - (&1:int) <= nth_i a (r + (&1:int)) in
  !a:int list. !i:int.
    decrease1 a ==>
    (&0:int) <= i ==>
    let o1 = &(LENGTH a) in
    (i < o1
     ==>
     (((&0:int) <= i /\ i < &(LENGTH a)) /\
      (~(nth_i a i = (&0:int))
       ==>
       (((&0:int) <= i /\ i < &(LENGTH a)) /\
        (if (&0:int) < nth_i a i then
           (((&0:int) <= i /\ i < &(LENGTH a)) /\
            (let o2 = i + nth_i a i in
             (((&0:int) <= &(LENGTH a) - i /\
               &(LENGTH a) - o2 < &(LENGTH a) - i) /\
              decrease1 a /\
              (&0:int) <= o2)))
         else
           let o2 = i + (&1:int) in
           (((&0:int) <= &(LENGTH a) - i /\
            &(LENGTH a) - o2 < &(LENGTH a) - i) /\
           decrease1 a /\
           (&0:int) <= o2)))))) /\
    (!result:int.
       (if i < o1 then
          if nth_i a i = (&0:int) then
            result = i
          else if (&0:int) < nth_i a i then
            let o2 = i + nth_i a i in
            (result = --(&1:int) /\
             (!j:int.
                o2 <= j /\ j < &(LENGTH a)
                ==> ~(nth_i a j = (&0:int)))) \/
            ((o2 <= result /\ result < &(LENGTH a)) /\
             nth_i a result = (&0:int) /\
             (!j:int.
                o2 <= j /\ j < result
                ==> ~(nth_i a j = (&0:int))))
          else
            let o2 = i + (&1:int) in
            (result = --(&1:int) /\
             (!j:int.
                o2 <= j /\ j < &(LENGTH a)
                ==> ~(nth_i a j = (&0:int)))) \/
            ((o2 <= result /\ result < &(LENGTH a)) /\
             nth_i a result = (&0:int) /\
             (!j:int.
                o2 <= j /\ j < result
                ==> ~(nth_i a j = (&0:int))))
        else
          result = --(&1:int))
       ==>
       (result = --(&1:int) /\
        (!j:int.
           i <= j /\ j < &(LENGTH a)
           ==> ~(nth_i a j = (&0:int)))) \/
       ((i <= result /\ result < &(LENGTH a)) /\
        nth_i a result = (&0:int) /\
        (!j:int.
           i <= j /\ j < result
           ==> ~(nth_i a j = (&0:int)))))`;;
