(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/cursor_examples_TestListCursor_list_sumqtvc: a list-cursor summation
  verification condition covering the initial invariant, cursor progress,
  decreasing length variant, and running-sum update. This file contains no
  proof.
*)

let statement =
 `!visited collection:A->int list.
  !c:A. !l:int list.
    let permitted =
      \(d:A).
        LENGTH (visited d) <= LENGTH (collection d) /\
        (!i:num.
           i < LENGTH (visited d)
           ==> EL i (visited d) = EL i (collection d)) in
    let complete =
      \(d:A). LENGTH (visited d) = LENGTH (collection d) in
    let list_sum =
      \(xs:int list). ITLIST (+) xs (&0:int) in
    permitted c
    ==>
    visited c = []
    ==>
    collection c = l
    ==>
    ((&0:int) = list_sum (visited c) /\
     permitted c /\
     (!c1:A.
        collection c1 = collection c
        ==>
        permitted c1
        ==>
        permitted c1 /\
        (if ~(complete c1) then
           (~(complete c1) /\ permitted c1) /\
           (!c2:A.
              collection c2 = collection c1
              ==>
              (!x:int.
                 visited c2 = APPEND (visited c1) [x] /\
                 permitted c2
                 ==>
                 (((&0:int) <=
                    (&(LENGTH l):int) - (&(LENGTH (visited c1)):int) /\
                   (&(LENGTH l):int) - (&(LENGTH (visited c2)):int) <
                    (&(LENGTH l):int) - (&(LENGTH (visited c1)):int)) /\
                  list_sum (visited c1) + x =
                    list_sum (visited c2) /\
                  permitted c2)))
         else
           list_sum (visited c1) = list_sum l)))`;;
