(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeArray_updateqtvc: the verification condition for
  updating an integer cumulative-sum array, including point-update framing,
  loop-invariant preservation, and the final cumulative-array specification.
  This file contains no proof.
*)

let sumrange_update_to_num = new_definition
 `sumrange_update_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let sumrange_update_nth = new_definition
 `sumrange_update_nth (a:int list) (i:int) =
    if i < (&0:int) then (&0:int)
    else if num_of_int i < LENGTH a
    then EL (num_of_int i) a
    else (&0:int)`;;

let sumrange_update_update_nat =
  new_recursive_definition list_RECURSION
   `(!n x:int. sumrange_update_update_nat [] n x = []) /\
    (!h:int.
     !t:int list.
     !n:num.
     !x:int.
       sumrange_update_update_nat (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (sumrange_update_update_nat t (PRE n) x))`;;

let sumrange_update_update = new_definition
 `sumrange_update_update (a:int list) (i:int) (x:int) =
    sumrange_update_update_nat a (sumrange_update_to_num i) x`;;

let sumrange_update_sum_nat =
  new_recursive_definition num_RECURSION
   `(!a:int list. !lower:int.
       sumrange_update_sum_nat a lower 0 = (&0:int)) /\
    (!a:int list. !lower:int. !n:num.
       sumrange_update_sum_nat a lower (SUC n) =
       sumrange_update_nth a lower +
       sumrange_update_sum_nat a (lower + (&1:int)) n)`;;

let sumrange_update_sum = new_definition
 `sumrange_update_sum (a:int list) (lower:int) (upper:int) =
    sumrange_update_sum_nat a lower
      (sumrange_update_to_num (upper - lower))`;;

let sumrange_update_is_cumulative_array_for = new_definition
 `sumrange_update_is_cumulative_array_for
    (c:int list) (a:int list) <=>
    (&(LENGTH c):int) = (&(LENGTH a):int) + (&1:int) /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH c):int)
       ==> sumrange_update_nth c i =
           sumrange_update_sum a (&0:int) i)`;;

let statement =
 `!c a:int list. !i v:int.
    sumrange_update_is_cumulative_array_for c a
    ==>
    (&0:int) <= i
    ==>
    i < (&(LENGTH a):int)
    ==>
    (&0:int) <= i /\
    i < (&(LENGTH c):int) /\
    (let o1 = i + (&1:int) in
     ((&0:int) <= o1 /\ o1 < (&(LENGTH c):int)) /\
     (let incr =
        v - sumrange_update_nth c o1 + sumrange_update_nth c i in
      ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
      (LENGTH (sumrange_update_update a i v) = LENGTH a
       ==>
       (\k:int. sumrange_update_nth
          (sumrange_update_update a i v) k) =
       (\k:int.
          if k = i then v else sumrange_update_nth a k)
       ==>
       (let o2 = (&(LENGTH c):int) - (&1:int) in
        let o3 = i + (&1:int) in
        (o3 <= o2 + (&1:int)
         ==>
         ((!k:int.
             o3 <= k /\ k < (&(LENGTH c):int)
             ==> sumrange_update_nth c k =
                 sumrange_update_sum
                   (sumrange_update_update a i v) (&0:int) k -
                 incr) /\
          (!k:int.
             (&0:int) <= k /\ k < o3
             ==> sumrange_update_nth c k =
                 sumrange_update_sum
                   (sumrange_update_update a i v) (&0:int) k) /\
          (!c1:int list.
             LENGTH c1 = LENGTH c
             ==>
             ((!j:int.
                 (((o3 <= j /\ j <= o2) /\
                   (!k:int.
                      j <= k /\ k < (&(LENGTH c1):int)
                      ==> sumrange_update_nth c1 k =
                          sumrange_update_sum
                            (sumrange_update_update a i v)
                            (&0:int) k -
                          incr) /\
                   (!k:int.
                      (&0:int) <= k /\ k < j
                      ==> sumrange_update_nth c1 k =
                          sumrange_update_sum
                            (sumrange_update_update a i v)
                            (&0:int) k))
                  ==>
                  ((&0:int) <= j /\ j < (&(LENGTH c1):int)) /\
                  (let o4 = sumrange_update_nth c1 j + incr in
                   ((&0:int) <= j /\ j < (&(LENGTH c1):int)) /\
                   (LENGTH (sumrange_update_update c1 j o4) =
                      LENGTH c1
                    ==>
                    (\k:int. sumrange_update_nth
                       (sumrange_update_update c1 j o4) k) =
                    (\k:int.
                       if k = j then o4 else sumrange_update_nth c1 k)
                    ==>
                    (!k:int.
                       j + (&1:int) <= k /\
                       k <
                         (&(LENGTH
                           (sumrange_update_update c1 j o4)):int)
                       ==> sumrange_update_nth
                             (sumrange_update_update c1 j o4) k =
                           sumrange_update_sum
                             (sumrange_update_update a i v)
                             (&0:int) k -
                           incr) /\
                    (!k:int.
                       (&0:int) <= k /\ k < j + (&1:int)
                       ==> sumrange_update_nth
                             (sumrange_update_update c1 j o4) k =
                           sumrange_update_sum
                             (sumrange_update_update a i v)
                             (&0:int) k))))) /\
              (((!k:int.
                   o2 + (&1:int) <= k /\
                   k < (&(LENGTH c1):int)
                   ==> sumrange_update_nth c1 k =
                       sumrange_update_sum
                         (sumrange_update_update a i v) (&0:int) k -
                       incr) /\
                (!k:int.
                   (&0:int) <= k /\ k < o2 + (&1:int)
                   ==> sumrange_update_nth c1 k =
                       sumrange_update_sum
                         (sumrange_update_update a i v) (&0:int) k))
               ==>
               sumrange_update_is_cumulative_array_for
                 c1 (sumrange_update_update a i v) /\
               sumrange_update_nth
                 (sumrange_update_update a i v) i = v /\
               (!k:int.
                  (((&0:int) <= k /\
                    k <
                      (&(LENGTH
                        (sumrange_update_update a i v)):int)) /\
                   ~(k = i))
                  ==> sumrange_update_nth
                        (sumrange_update_update a i v) k =
                      sumrange_update_nth a k)))))
         /\
         (o2 + (&1:int) < o3
          ==>
          sumrange_update_is_cumulative_array_for
            c (sumrange_update_update a i v) /\
          sumrange_update_nth
            (sumrange_update_update a i v) i = v /\
          (!k:int.
             (((&0:int) <= k /\
               k <
                 (&(LENGTH (sumrange_update_update a i v)):int)) /\
              ~(k = i))
             ==> sumrange_update_nth
                   (sumrange_update_update a i v) k =
                 sumrange_update_nth a k)))))))`;;
