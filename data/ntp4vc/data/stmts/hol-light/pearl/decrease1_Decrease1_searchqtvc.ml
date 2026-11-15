(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/decrease1_Decrease1_searchqtvc: an integer-list search-loop
  verification condition for a sequence that decreases by at most one,
  covering zero detection, forward progress, and absence of earlier zeros.
  This file contains no proof.
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
  !a:int list.
    decrease1 a ==>
    (&0:int) <= (&0:int) /\
    (!j:int.
       (&0:int) <= j /\ j < (&0:int)
       ==> j < &(LENGTH a)
       ==> ~(nth_i a j = (&0:int))) /\
    (!i:int.
       (&0:int) <= i /\
       (!j:int.
          (&0:int) <= j /\ j < i
          ==> j < &(LENGTH a)
          ==> ~(nth_i a j = (&0:int)))
       ==>
       if i < &(LENGTH a) then
         ((&0:int) <= i /\ i < &(LENGTH a)) /\
         (if nth_i a i = (&0:int) then
            (i = --(&1:int) /\
             (!j:int.
                (&0:int) <= j /\ j < &(LENGTH a)
                ==> ~(nth_i a j = (&0:int)))) \/
            (((&0:int) <= i /\ i < &(LENGTH a)) /\
             nth_i a i = (&0:int) /\
             (!j:int.
                (&0:int) <= j /\ j < i
                ==> ~(nth_i a j = (&0:int))))
          else
            ((&0:int) <= i /\ i < &(LENGTH a)) /\
            (if (&0:int) < nth_i a i then
               (((&0:int) <= i /\ i < &(LENGTH a)) /\
                ((&0:int) <= &(LENGTH a) - i /\
                 &(LENGTH a) - (i + nth_i a i) <
                   &(LENGTH a) - i) /\
                (&0:int) <= i + nth_i a i /\
                (!j:int.
                   (&0:int) <= j /\ j < i + nth_i a i
                   ==> j < &(LENGTH a)
                   ==> ~(nth_i a j = (&0:int))))
             else
               (((&0:int) <= &(LENGTH a) - i /\
                 &(LENGTH a) - (i + (&1:int)) <
                   &(LENGTH a) - i) /\
                (&0:int) <= i + (&1:int) /\
                (!j:int.
                   (&0:int) <= j /\ j < i + (&1:int)
                   ==> j < &(LENGTH a)
                   ==> ~(nth_i a j = (&0:int))))))
       else
         (!j:int.
            (&0:int) <= j /\ j < &(LENGTH a)
            ==> ~(nth_i a j = (&0:int))) \/
         (((&0:int) <= --(&1:int) /\
           --(&1:int) < &(LENGTH a)) /\
          nth_i a (--(&1:int)) = (&0:int) /\
          (!j:int.
             (&0:int) <= j /\ j < --(&1:int)
             ==> ~(nth_i a j = (&0:int)))))`;;
