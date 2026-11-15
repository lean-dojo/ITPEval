(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/euler_sieve_EulerSieveImpl_createqtvc: the creation verification
  condition for an Euler sieve, including 63-bit bounds, initialized successor
  and marking arrays, array-filling loop invariants, and the resulting sieve
  state invariant and parity properties. This file contains no proof.
*)

needs "Library/words.ml";;

let euler_sieve_nth = new_definition
 `euler_sieve_nth (d:A) (a:A list) (i:int) =
    if a = [] then d
    else if i < (&0:int) then EL 0 a
    else if num_of_int i < LENGTH a then EL (num_of_int i) a
    else d`;;

let euler_sieve_update_nat =
  new_recursive_definition list_RECURSION
   `(!n x:A. euler_sieve_update_nat [] n x = []) /\
    (!h:A. !t:A list. !n:num. !x:A.
       euler_sieve_update_nat (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (euler_sieve_update_nat t (PRE n) x))`;;

let euler_sieve_update = new_definition
 `euler_sieve_update (a:A list) (i:int) (x:A) =
    if i < (&0:int)
    then euler_sieve_update_nat a 0 x
    else euler_sieve_update_nat a (num_of_int i) x`;;

let euler_sieve_create = new_definition
 `euler_sieve_create (n:int) (f:int->A) =
    list_of_seq (\k. f (&k)) (num_of_int n)`;;

let euler_sieve_int63_in_bounds = new_definition
 `euler_sieve_int63_in_bounds (x:int) <=>
    --(&2 pow 62) <= x /\ x <= &2 pow 62 - (&1:int)`;;

let euler_sieve_array_inv = new_definition
 `euler_sieve_array_inv (elts:B->int list) (size:B->int) <=>
    !self:B.
      (&0:int) <= size self /\
      size self = (&(LENGTH (elts self)):int) /\
      (&(LENGTH (elts self)):int) <= &2 pow 62 - (&1:int) /\
      (!i:int.
         (&0:int) <= i /\ i < (&(LENGTH (elts self)):int)
         ==> euler_sieve_int63_in_bounds
               (euler_sieve_nth (&0:int) (elts self) i))`;;

let euler_sieve_tdiv = new_definition
 `euler_sieve_tdiv (x:int) (y:int) =
    int_sgn x * int_sgn y * (abs x div abs y)`;;

let euler_sieve_inv_nexts = new_definition
 `euler_sieve_inv_nexts (nexts:int list) (n:int) <=>
    !i:int.
      (&0:int) <= i /\ i < n
      ==> i < euler_sieve_nth (&0:int) nexts i /\
          euler_sieve_nth (&0:int) nexts i <= n`;;

let euler_sieve_all_eliminated_marked = new_definition
 `euler_sieve_all_eliminated_marked
    (marked:bool list) (nexts:int list) <=>
    LENGTH marked = LENGTH nexts /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH marked):int)
       ==> !j:int.
             i < j /\ j < euler_sieve_nth (&0:int) nexts i
             ==> euler_sieve_nth F marked j = T)`;;

let euler_sieve_fc = new_definition
 `euler_sieve_fc (max1:(63)word) (i:int) =
    if i = ival max1 then ival max1 + (&1:int)
    else if i = ival max1 - (&1:int) then
      if i rem (&2:int) = (&0:int)
      then ival max1
      else ival max1 + (&1:int)
    else if i < (&3:int) \/ i rem (&2:int) = (&0:int)
    then i + (&1:int)
    else i + (&2:int)`;;

let euler_sieve_o1 = new_definition
 `euler_sieve_o1 (i:int) <=>
    i = (&0:int) \/ i = (&1:int) \/
    (&2:int) < i /\ i rem (&2:int) = (&0:int)`;;

let euler_sieve_fc1 = new_definition
 `euler_sieve_fc1
    (max1:(63)word) (len_arr:(63)word) (i:int) =
    if i = ival len_arr - (&1:int)
    then ival max1 + (&1:int)
    else if i = (&0:int)
    then --(&2:int)
    else (&2:int) * i + (&3:int)`;;

let euler_sieve_state_inv = new_definition
 `euler_sieve_state_inv
    (elts:B->int list)
    (nexts:int list) (marked:bool list) (arr:B)
    (maxv:int) (maxarrv:int) <=>
    maxv < &2 pow 62 - (&1:int) /\
    (&3:int) <= maxv /\
    LENGTH nexts = LENGTH marked /\
    (&(LENGTH marked):int) = maxv + (&1:int) /\
    (maxv - (&1:int)) div (&2:int) = maxarrv /\
    (&(LENGTH (elts arr)):int) = maxarrv + (&1:int) /\
    euler_sieve_inv_nexts nexts (&(LENGTH nexts):int) /\
    euler_sieve_all_eliminated_marked marked nexts /\
    (!i:int.
       (&3:int) <= i /\ i <= maxv
       ==> i rem (&2:int) = (&0:int)
       ==> euler_sieve_nth F marked i = T) /\
    (!i:int.
       (&3:int) <= i /\ i < maxv - (&1:int)
       ==> i rem (&2:int) = (&1:int)
       ==> euler_sieve_nth (&0:int) nexts i rem (&2:int) = (&1:int) \/
           euler_sieve_nth (&0:int) nexts i = maxv + (&1:int)) /\
    euler_sieve_nth (&0:int) nexts maxv = maxv + (&1:int) /\
    ((maxv - (&1:int)) rem (&2:int) = (&0:int)
     ==> euler_sieve_nth (&0:int) nexts (maxv - (&1:int)) = maxv) /\
    ((maxv - (&1:int)) rem (&2:int) = (&1:int)
     ==> euler_sieve_nth (&0:int) nexts (maxv - (&1:int)) =
         maxv + (&1:int)) /\
    (!i:int.
       (&0:int) <= i /\ i <= maxarrv
       ==> --(maxv + (&1:int)) <=
           euler_sieve_nth (&0:int) (elts arr) i /\
           euler_sieve_nth (&0:int) (elts arr) i <=
           maxv + (&1:int)) /\
    (!i:int.
       (&0:int) <= i /\ i <= maxarrv
       ==> (euler_sieve_nth F marked ((&2:int) * i + (&1:int)) = T <=>
            euler_sieve_nth (&0:int) (elts arr) i <
            (&0:int))) /\
    (!i:int.
       (&0:int) <= i /\ i <= maxarrv
       ==> ~(euler_sieve_nth F marked ((&2:int) * i + (&1:int)) = T)
       ==> euler_sieve_nth (&0:int) (elts arr) i =
           euler_sieve_nth (&0:int) nexts ((&2:int) * i + (&1:int))) /\
    (!i:int.
       (&0:int) <= i /\ i <= maxarrv
       ==> euler_sieve_nth F marked ((&2:int) * i + (&1:int)) = T
       ==> euler_sieve_nth (&0:int) (elts arr) i =
           --(euler_sieve_nth (&0:int) nexts
                ((&2:int) * i + (&1:int)))) /\
    (!i:int.
       (&0:int) <= i /\ i <= maxarrv
       ==> (i <
            abs (euler_sieve_nth (&0:int) (elts arr) i)
              div (&2:int) /\
            abs (euler_sieve_nth (&0:int) (elts arr) i)
              div (&2:int) <= maxarrv + (&1:int)) /\
           abs (euler_sieve_nth (&0:int) (elts arr) i) <=
           maxv + (&1:int)) /\
    (!i j:int.
       (&0:int) <= i /\ i <= maxarrv
       ==> i < j /\
           j <
           abs (euler_sieve_nth (&0:int) (elts arr) i)
             div (&2:int)
       ==> euler_sieve_nth (&0:int) (elts arr) j <
           (&0:int))`;;

let euler_sieve_result_post = new_definition
 `euler_sieve_result_post
    (nexts:A->int list) (marked:A->bool list)
    (maxf:A->(63)word) (max1:(63)word) (result:A) <=>
    maxf result = max1 /\
    ((euler_sieve_nth F (marked result) (&0:int) =
      euler_sieve_nth F (marked result) (&1:int) /\
      euler_sieve_nth F (marked result) (&1:int) = T) /\
     ~(euler_sieve_nth F (marked result) (&2:int) = T)) /\
    (!i:int.
       (&1:int) <= i /\
       i <= (ival max1 - (&1:int)) div (&2:int)
       ==> ~(euler_sieve_nth F (marked result)
               ((&2:int) * i + (&1:int)) = T)) /\
    (!i:int.
       (&2:int) <= i /\
       i <= (ival max1 + (&1:int)) div (&2:int)
       ==> (&2:int) * i <= ival max1
       ==> euler_sieve_nth F (marked result) ((&2:int) * i) = T) /\
    (!i:int.
       (&1:int) <= i /\
       i <= (ival max1 - (&1:int)) div (&2:int)
       ==> (&2:int) * i + (&1:int) < ival max1 - (&1:int)
       ==> euler_sieve_nth (&0:int) (nexts result)
             ((&2:int) * i + (&1:int)) =
           (&2:int) * i + (&3:int)) /\
    (!i:int.
       (&2:int) <= i /\
       i <= (ival max1 - (&1:int)) div (&2:int)
       ==> (&2:int) * i < ival max1 - (&1:int)
       ==> euler_sieve_nth (&0:int) (nexts result) ((&2:int) * i) =
           (&2:int) * i + (&1:int)) /\
    (!i:int.
       (&0:int) <= i /\ i <= ival max1
       ==> euler_sieve_nth F (marked result) i = T
       ==> i < (&2:int) \/ (&2:int) divides i)`;;

let euler_sieve_finish = new_definition
 `euler_sieve_finish
    (elts:B->int list)
    (nexts:A->int list) (marked:A->bool list)
    (arr:A->B) (maxf:A->(63)word)
    (maxarrf:A->(63)word)
    (max1:(63)word) (nexts1:int list) (marked1:bool list)
    (arrx:B) <=>
    euler_sieve_int63_in_bounds (ival max1 - (&1:int)) /\
    (!o7:(63)word.
       ival o7 = ival max1 - (&1:int)
       ==> ~((&2:int) = (&0:int)) /\
           euler_sieve_int63_in_bounds
             (euler_sieve_tdiv (ival o7) (&2:int)) /\
           (!o8:(63)word.
              ival o8 = euler_sieve_tdiv (ival o7) (&2:int)
              ==> euler_sieve_state_inv
                    elts nexts1 marked1 arrx (ival max1) (ival o8) /\
                  (!result:A.
                     nexts result = nexts1 /\
                     marked result = marked1 /\
                     arr result = arrx /\
                     maxf result = max1 /\
                     maxarrf result = o8
                     ==> euler_sieve_result_post
                           nexts marked maxf max1 result)))`;;

let statement =
 `!elts:B->int list.
  !size:B->int.
  !nexts:A->int list.
  !marked:A->bool list.
  !arr:A->B.
  !maxf:A->(63)word.
  !maxarrf:A->(63)word.
  !max1:(63)word.
    (euler_sieve_array_inv elts size /\
     (!self:A.
        euler_sieve_state_inv
          elts (nexts self) (marked self) (arr self)
          (ival (maxf self)) (ival (maxarrf self))) /\
     (!a b:A.
        nexts a = nexts b /\
        marked a = marked b /\
        arr a = arr b /\
        maxf a = maxf b /\
        maxarrf a = maxarrf b
        ==> a = b))
    ==>
    ival max1 < &2 pow 62 - (&1:int)
    ==>
    (&3:int) <= ival max1
    ==>
    let len = ival max1 + (&1:int) in
    euler_sieve_int63_in_bounds (ival max1 - (&1:int)) /\
    (!o2:(63)word.
       ival o2 = ival max1 - (&1:int)
       ==> (~((&2:int) = (&0:int)) /\
            euler_sieve_int63_in_bounds
              (euler_sieve_tdiv (ival o2) (&2:int))) /\
           (!o3:(63)word.
              ival o3 = euler_sieve_tdiv (ival o2) (&2:int)
              ==> euler_sieve_int63_in_bounds (ival o3 + (&1:int)) /\
                  (!len_arr:(63)word.
                     ival len_arr = ival o3 + (&1:int)
                     ==>
                     let o4 = euler_sieve_fc max1 in
                     (&0:int) <= len /\
                     let nexts1 = euler_sieve_create len o4 in
                     ((&(LENGTH nexts1):int) = len /\
                       (!i:int.
                          (&0:int) <= i /\ i < len
                          ==> euler_sieve_nth (&0:int) nexts1 i = o4 i))
                      ==>
                      (!i:int.
                         ~(i = (&0:int))
                         ==> ~(i = (&1:int))
                         ==> (&2:int) < i
                         ==> ~((&2:int) = (&0:int))) /\
                      (let o5 = euler_sieve_o1 in
                       (&0:int) <= len /\
                       let marked1 = euler_sieve_create len o5 in
                       ((&(LENGTH marked1):int) = len /\
                         (!i:int.
                            (&0:int) <= i /\ i < len
                            ==> euler_sieve_nth F marked1 i = o5 i))
                        ==>
                        let f = euler_sieve_fc1 max1 len_arr in
                        (&0:int) <= ival len_arr /\
                        (!arr1:B.
                           (!i:int.
                              (&0:int) <= i /\ i < ival len_arr
                              ==> euler_sieve_nth (&0:int)
                                    (elts arr1) i =
                                  --(&2:int)) /\
                           (&(LENGTH (elts arr1)):int) =
                             ival len_arr
                           ==> euler_sieve_int63_in_bounds
                                 (ival len_arr - (&1:int)) /\
                               (!o6:(63)word.
                                  ival o6 = ival len_arr - (&1:int)
                                  ==>
                                  (((&1:int) <= ival o6 + (&1:int)
                                    ==>
                                    (!j:int.
                                       (&0:int) <= j /\ j < (&1:int)
                                       ==> euler_sieve_nth (&0:int)
                                             (elts arr1) j =
                                           f j) /\
                                    (!arr2:B.
                                       size arr2 = size arr1
                                       ==>
                                       ((!i:(63)word.
                                           let i1 = ival i in
                                           (((&1:int) <= i1 /\
                                             i1 <= ival o6) /\
                                            (!j:int.
                                               (&0:int) <= j /\ j < i1
                                               ==> euler_sieve_nth (&0:int)
                                                     (elts arr2)
                                                     j = f j))
                                           ==>
                                           euler_sieve_int63_in_bounds
                                             (ival len_arr - (&1:int)) /\
                                           (!o7:(63)word.
                                              ival o7 =
                                                ival len_arr - (&1:int)
                                              ==>
                                              (ival i = ival o7 ==> i = o7)
                                              ==>
                                              (if i = o7 then
                                                 euler_sieve_int63_in_bounds
                                                   (ival max1 + (&1:int))
                                               else
                                                 euler_sieve_int63_in_bounds
                                                   ((&2:int) * ival i) /\
                                                 (!o8:(63)word.
                                                    ival o8 =
                                                      (&2:int) * ival i
                                                    ==>
                                                    euler_sieve_int63_in_bounds
                                                      (ival o8 + (&3:int)))) /\
                                              (!o8:(63)word.
                                                 (if i = o7 then
                                                    ival o8 =
                                                      ival max1 + (&1:int)
                                                  else
                                                    ?o9:(63)word.
                                                      ival o9 =
                                                        (&2:int) * ival i /\
                                                      ival o8 =
                                                        ival o9 + (&3:int))
                                                 ==>
                                                 ((&0:int) <= ival i /\
                                                  ival i <
                                                    (&(LENGTH
                                                       (elts arr2)):int)) /\
                                                 (!arr3:B.
                                                    size arr3 =
                                                      size arr2
                                                    ==>
                                                    elts arr3 =
                                                      euler_sieve_update
                                                        (elts arr2)
                                                        (ival i) (ival o8)
                                                    ==>
                                                    !j:int.
                                                      (&0:int) <= j /\
                                                      j < i1 + (&1:int)
                                                      ==>
                                                      euler_sieve_nth
                                                        (&0:int)
                                                        (elts arr3)
                                                        j = f j))))) /\
                                        (((!j:int.
                                             (&0:int) <= j /\
                                             j < ival o6 + (&1:int)
                                             ==> euler_sieve_nth (&0:int)
                                                   (elts arr2) j =
                                                 f j)
                                          ==>
                                          euler_sieve_finish
                                            elts nexts marked arr maxf maxarrf
                                            max1 nexts1 marked1 arr2))))
                                   /\
                                   (ival o6 + (&1:int) < (&1:int)
                                    ==>
                                    euler_sieve_finish
                                      elts nexts marked arr maxf maxarrf
                                      max1 nexts1 marked1 arr1))))))))`;;
