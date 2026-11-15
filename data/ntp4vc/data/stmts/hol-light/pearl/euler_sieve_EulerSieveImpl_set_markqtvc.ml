(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/euler_sieve_EulerSieveImpl_set_markqtvc: the verification condition
  for marking an odd index in an Euler sieve while updating its compact
  successor array and preserving the sieve state invariant. This file contains
  no proof.
*)

needs "Library/words.ml";;

let euler_sieve_set_mark_nth = new_definition
 `euler_sieve_set_mark_nth (d:A) (a:A list) (i:int) =
    if a = [] then d
    else if i < (&0:int) then EL 0 a
    else if num_of_int i < LENGTH a then EL (num_of_int i) a
    else d`;;

let euler_sieve_set_mark_update_nat =
  new_recursive_definition list_RECURSION
   `(!n x:A. euler_sieve_set_mark_update_nat [] n x = []) /\
    (!h:A. !t:A list. !n:num. !x:A.
       euler_sieve_set_mark_update_nat (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h
              (euler_sieve_set_mark_update_nat t (PRE n) x))`;;

let euler_sieve_set_mark_update = new_definition
 `euler_sieve_set_mark_update (a:A list) (i:int) (x:A) =
    if i < (&0:int)
    then euler_sieve_set_mark_update_nat a 0 x
    else euler_sieve_set_mark_update_nat a (num_of_int i) x`;;

let euler_sieve_set_mark_int63_in_bounds = new_definition
 `euler_sieve_set_mark_int63_in_bounds (x:int) <=>
    --(&2 pow 62) <= x /\ x <= &2 pow 62 - (&1:int)`;;

let euler_sieve_set_mark_array_inv = new_definition
 `euler_sieve_set_mark_array_inv
    (elts:B->int list) (size:B->int) (a:B) <=>
    (&0:int) <= size a /\
    size a = (&(LENGTH (elts a)):int) /\
    (&(LENGTH (elts a)):int) <= &2 pow 62 - (&1:int) /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH (elts a)):int)
       ==> euler_sieve_set_mark_int63_in_bounds
             (euler_sieve_set_mark_nth (&0:int) (elts a) i))`;;

let euler_sieve_set_mark_tdiv = new_definition
 `euler_sieve_set_mark_tdiv (x:int) (y:int) =
    int_sgn x * int_sgn y * (abs x div abs y)`;;

let euler_sieve_set_mark_inv_nexts = new_definition
 `euler_sieve_set_mark_inv_nexts (nexts:int list) (n:int) <=>
    !i:int.
      (&0:int) <= i /\ i < n
      ==> i < euler_sieve_set_mark_nth (&0:int) nexts i /\
          euler_sieve_set_mark_nth (&0:int) nexts i <= n`;;

let euler_sieve_set_mark_all_eliminated = new_definition
 `euler_sieve_set_mark_all_eliminated
    (marked:bool list) (nexts:int list) <=>
    LENGTH marked = LENGTH nexts /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH marked):int)
       ==> !j:int.
             i < j /\ j < euler_sieve_set_mark_nth (&0:int) nexts i
             ==> euler_sieve_set_mark_nth F marked j = T)`;;

let euler_sieve_set_mark_state_inv = new_definition
 `euler_sieve_set_mark_state_inv
    (nexts:int list) (marked:bool list) (arr:B) (elts:B->int list)
    (maxv:int) (maxarrv:int) <=>
    maxv < &2 pow 62 - (&1:int) /\
    (&3:int) <= maxv /\
    LENGTH nexts = LENGTH marked /\
    (&(LENGTH marked):int) = maxv + (&1:int) /\
    (maxv - (&1:int)) div (&2:int) = maxarrv /\
    (&(LENGTH (elts arr)):int) =
      maxarrv + (&1:int) /\
    euler_sieve_set_mark_inv_nexts
      nexts (&(LENGTH nexts):int) /\
    euler_sieve_set_mark_all_eliminated marked nexts /\
    (!i:int.
       (&3:int) <= i /\ i <= maxv
       ==> i rem (&2:int) = (&0:int)
       ==> euler_sieve_set_mark_nth F marked i = T) /\
    (!i:int.
       (&3:int) <= i /\ i < maxv - (&1:int)
       ==> i rem (&2:int) = (&1:int)
       ==> euler_sieve_set_mark_nth (&0:int) nexts i rem (&2:int) =
             (&1:int) \/
           euler_sieve_set_mark_nth (&0:int) nexts i =
             maxv + (&1:int)) /\
    euler_sieve_set_mark_nth (&0:int) nexts maxv =
      maxv + (&1:int) /\
    ((maxv - (&1:int)) rem (&2:int) = (&0:int)
     ==> euler_sieve_set_mark_nth
           (&0:int) nexts (maxv - (&1:int)) = maxv) /\
    ((maxv - (&1:int)) rem (&2:int) = (&1:int)
     ==> euler_sieve_set_mark_nth
           (&0:int) nexts (maxv - (&1:int)) = maxv + (&1:int)) /\
    (!i:int.
       (&0:int) <= i /\ i <= maxarrv
       ==> --(maxv + (&1:int)) <=
           euler_sieve_set_mark_nth
             (&0:int) (elts arr) i /\
           euler_sieve_set_mark_nth
             (&0:int) (elts arr) i <=
           maxv + (&1:int)) /\
    (!i:int.
       (&0:int) <= i /\ i <= maxarrv
       ==> (euler_sieve_set_mark_nth
              F marked ((&2:int) * i + (&1:int)) = T <=>
            euler_sieve_set_mark_nth
              (&0:int) (elts arr) i < (&0:int))) /\
    (!i:int.
       (&0:int) <= i /\ i <= maxarrv
       ==> ~(euler_sieve_set_mark_nth
               F marked ((&2:int) * i + (&1:int)) = T)
       ==> euler_sieve_set_mark_nth
             (&0:int) (elts arr) i =
           euler_sieve_set_mark_nth
             (&0:int) nexts ((&2:int) * i + (&1:int))) /\
    (!i:int.
       (&0:int) <= i /\ i <= maxarrv
       ==> euler_sieve_set_mark_nth
             F marked ((&2:int) * i + (&1:int)) = T
       ==> euler_sieve_set_mark_nth
             (&0:int) (elts arr) i =
           --(euler_sieve_set_mark_nth
                (&0:int) nexts ((&2:int) * i + (&1:int)))) /\
    (!i:int.
       (&0:int) <= i /\ i <= maxarrv
       ==> (i <
            abs (euler_sieve_set_mark_nth
                   (&0:int) (elts arr) i)
              div (&2:int) /\
            abs (euler_sieve_set_mark_nth
                   (&0:int) (elts arr) i)
              div (&2:int) <= maxarrv + (&1:int)) /\
           abs (euler_sieve_set_mark_nth
                  (&0:int) (elts arr) i) <=
           maxv + (&1:int)) /\
    (!i j:int.
       (&0:int) <= i /\ i <= maxarrv
       ==> i < j /\
           j <
           abs (euler_sieve_set_mark_nth
                  (&0:int) (elts arr) i)
             div (&2:int)
       ==> euler_sieve_set_mark_nth
             (&0:int) (elts arr) j < (&0:int))`;;

let statement =
 `!nexts:A->int list.
  !marked:A->bool list.
  !arr:A->B.
  !maxf:A->(63)word.
  !maxarrf:A->(63)word.
  !elts:B->int list.
  !size:B->int.
    ((!a:B.
        euler_sieve_set_mark_array_inv elts size a) /\
     (!self:A.
        euler_sieve_set_mark_state_inv
          (nexts self) (marked self) (arr self) elts
          (ival (maxf self)) (ival (maxarrf self))) /\
     (!a b:A.
        nexts a = nexts b /\
        marked a = marked b /\
        arr a = arr b /\
        maxf a = maxf b /\
        maxarrf a = maxarrf b
        ==> a = b))
    ==>
    !i:(63)word.
    !t1:A.
      (&0:int) <= ival i
      ==> ival i <= ival (maxf t1)
      ==> ival i rem (&2:int) = (&1:int)
      ==> ~((&2:int) = (&0:int)) /\
          euler_sieve_set_mark_int63_in_bounds
            (euler_sieve_set_mark_tdiv (ival i) (&2:int)) /\
          (!x:(63)word.
             ival x =
               euler_sieve_set_mark_tdiv (ival i) (&2:int)
             ==>
             let o1 = arr t1 in
             ((&0:int) <= ival x /\
              ival x <
                (&(LENGTH (elts o1)):int)) /\
             (!o2:(63)word.
                ival o2 =
                  euler_sieve_set_mark_nth
                    (&0:int) (elts o1) (ival x)
                ==>
                if (&0:int) <= ival o2 then
                  let o3 = arr t1 in
                  ((&0:int) <= ival x /\
                   ival x <
                     (&(LENGTH (elts o3)):int)) /\
                  (!o4:(63)word.
                     ival o4 =
                       euler_sieve_set_mark_nth
                         (&0:int) (elts o3) (ival x)
                     ==>
                     euler_sieve_set_mark_int63_in_bounds
                       (--(ival o4)) /\
                     (!o5:(63)word.
                        ival o5 = --(ival o4)
                        ==>
                        let o6 = arr t1 in
                        ((&0:int) <= ival x /\
                         ival x <
                           (&(LENGTH (elts o6)):int)) /\
                        (!t_arr:B.
                           size t_arr = size o6
                           ==> size t_arr = size (arr t1)
                           ==> elts t_arr =
                               euler_sieve_set_mark_update
                                 (elts o6)
                                 (ival x) (ival o5)
                           ==>
                           let o7 = T in
                           let o8 = ival i in
                           ((&0:int) <= o8 /\
                            o8 < (&(LENGTH (marked t1)):int)) /\
                           (let o9 =
                              euler_sieve_set_mark_update
                                (marked t1) o8 o7 in
                            (LENGTH o9 = LENGTH (marked t1) /\
                             euler_sieve_set_mark_nth F o9 o8 = o7 /\
                             (!j:int.
                                ((&0:int) <= j /\
                                 j < (&(LENGTH (marked t1)):int)) /\
                                ~(j = o8)
                                ==> euler_sieve_set_mark_nth F o9 j =
                                    euler_sieve_set_mark_nth
                                      F (marked t1) j))
                            ==>
                            (!t2:A.
                               euler_sieve_set_mark_state_inv
                                 (nexts t1) o9 t_arr elts
                                 (ival (maxf t1))
                                 (ival (maxarrf t1)) /\
                               (maxarrf t1 = maxarrf t2 /\
                                maxf t1 = maxf t2 /\
                                t_arr = arr t2 /\
                                o9 = marked t2 /\
                                nexts t1 = nexts t2
                                ==> marked t2 =
                                    euler_sieve_set_mark_update
                                      (marked t1) (ival i) T))))))
                else
                  let o3 = T in
                  let o4 = ival i in
                  let o5 = marked t1 in
                  ((&0:int) <= o4 /\
                   o4 < (&(LENGTH o5):int)) /\
                  (let o6 =
                     euler_sieve_set_mark_update o5 o4 o3 in
                   (LENGTH o6 = LENGTH o5 /\
                    euler_sieve_set_mark_nth F o6 o4 = o3 /\
                    (!j:int.
                       ((&0:int) <= j /\
                        j < (&(LENGTH o5):int)) /\
                       ~(j = o4)
                       ==> euler_sieve_set_mark_nth F o6 j =
                           euler_sieve_set_mark_nth F o5 j))
                   ==>
                   (!t2:A.
                      euler_sieve_set_mark_state_inv
                        (nexts t1) o6 (arr t1) elts
                        (ival (maxf t1)) (ival (maxarrf t1)) /\
                      (maxarrf t1 = maxarrf t2 /\
                       maxf t1 = maxf t2 /\
                       arr t1 = arr t2 /\
                       o6 = marked t2 /\
                       nexts t1 = nexts t2
                       ==> marked t2 =
                           euler_sieve_set_mark_update
                             (marked t1) (ival i) T)))))`;;
