(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeArray_createqtvc: the verification condition for
  creating an integer cumulative-sum array, including zero initialization,
  loop-invariant preservation, and the final prefix-sum specification. This
  file contains no proof.
*)

needs "Library/isum.ml";;

let sumrange_create_to_num = new_definition
 `sumrange_create_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let sumrange_create_nth = new_definition
 `sumrange_create_nth (a:int list) (i:int) =
    if sumrange_create_to_num i < LENGTH a
    then EL (sumrange_create_to_num i) a
    else (&0:int)`;;

let sumrange_create_update_nat =
  new_recursive_definition list_RECURSION
   `(!n x:int. sumrange_create_update_nat [] n x = []) /\
    (!h:int.
     !t:int list.
     !n:num.
     !x:int.
       sumrange_create_update_nat (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (sumrange_create_update_nat t (PRE n) x))`;;

let sumrange_create_update = new_definition
 `sumrange_create_update (a:int list) (i:int) (x:int) =
    sumrange_create_update_nat a (sumrange_create_to_num i) x`;;

let sumrange_create_sum = new_definition
 `sumrange_create_sum (a:int list) (lower:int) (upper:int) =
    if upper <= lower then (&0:int)
    else
      isum (0..num_of_int (upper - lower) - 1)
        (\k. sumrange_create_nth a (lower + &k))`;;

let sumrange_create_is_cumulative_array_for = new_definition
 `sumrange_create_is_cumulative_array_for
    (c:int list) (a:int list) <=>
    (&(LENGTH c):int) = (&(LENGTH a):int) + (&1:int) /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH c):int)
       ==> sumrange_create_nth c i =
           sumrange_create_sum a (&0:int) i)`;;

let statement =
 `!a:int list.
    let l = (&(LENGTH a):int) in
    let o1 = l + (&1:int) in
    (&0:int) <= o1 /\
    (!s:int list.
       ((!i:int.
           (&0:int) <= i /\ i < o1
           ==> sumrange_create_nth s i = (&0:int)) /\
        (&(LENGTH s):int) = o1)
       ==>
       (((&1:int) <= l + (&1:int)
         ==>
         (!k:int.
            (&0:int) <= k /\ k < (&1:int)
            ==> sumrange_create_nth s k =
                sumrange_create_sum a (&0:int) k) /\
         (!s1:int list.
            LENGTH s1 = LENGTH s
            ==>
            ((!i:int.
                (((&1:int) <= i /\ i <= l) /\
                 (!k:int.
                    (&0:int) <= k /\ k < i
                    ==> sumrange_create_nth s1 k =
                        sumrange_create_sum a (&0:int) k))
                ==>
                let o2 = i - (&1:int) in
                ((&0:int) <= o2 /\ o2 < (&(LENGTH a):int)) /\
                (let o3 = i - (&1:int) in
                 ((&0:int) <= o3 /\
                  o3 < (&(LENGTH s1):int)) /\
                 (let o4 =
                    sumrange_create_nth s1 o3 +
                    sumrange_create_nth a o2 in
                  ((&0:int) <= i /\
                   i < (&(LENGTH s1):int)) /\
                  (LENGTH (sumrange_create_update s1 i o4) =
                     LENGTH s1
                   ==>
                   (\r:int.
                      sumrange_create_nth
                        (sumrange_create_update s1 i o4) r) =
                     (\r:int.
                        if r = i then o4
                        else sumrange_create_nth s1 r)
                   ==>
                   (!k:int.
                      (&0:int) <= k /\ k < i + (&1:int)
                      ==> sumrange_create_nth
                            (sumrange_create_update s1 i o4) k =
                          sumrange_create_sum a (&0:int) k))))) /\
             ((!k:int.
                 (&0:int) <= k /\ k < l + (&1:int)
                 ==> sumrange_create_nth s1 k =
                     sumrange_create_sum a (&0:int) k)
              ==>
              sumrange_create_is_cumulative_array_for s1 a))))
        /\
        (l + (&1:int) < (&1:int)
         ==> sumrange_create_is_cumulative_array_for s a)))`;;
