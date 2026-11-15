(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2017_odd_even_sort_rearranging_Top_odd_even_sortqtvc:
  the verification condition for odd-even sorting an integer array, including
  permutation, parity-indexed ordering invariants, swaps, entropy decrease,
  termination measures, and final sortedness. This file contains no proof.
*)

let odd_even_sort_to_num = new_definition
 `odd_even_sort_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let odd_even_sort_nth = new_definition
 `odd_even_sort_nth (a:int list) (i:int) =
    if odd_even_sort_to_num i < LENGTH a
    then EL (odd_even_sort_to_num i) a
    else (&0:int)`;;

let odd_even_sort_update =
  new_recursive_definition list_RECURSION
   `(!n:num. !x:int.
       odd_even_sort_update [] n x = []) /\
    (!h:int. !t:int list. !n:num. !x:int.
       odd_even_sort_update (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (odd_even_sort_update t (PRE n) x))`;;

let odd_even_sort_exchange = new_definition
 `odd_even_sort_exchange
    (before:int list) (after:int list) (i:int) (j:int) <=>
    after =
      odd_even_sort_update
        (odd_even_sort_update
          before
          (odd_even_sort_to_num i)
          (odd_even_sort_nth before j))
        (odd_even_sort_to_num j)
        (odd_even_sort_nth before i)`;;

let odd_even_sort_permut = new_definition
 `odd_even_sort_permut (a:int list) (b:int list) <=>
    LENGTH a = LENGTH b /\
    (!v:int.
       CARD {k:num | k < LENGTH a /\ EL k a = v} =
       CARD {k:num | k < LENGTH b /\ EL k b = v})`;;

let odd_even_sort_sorted = new_definition
 `odd_even_sort_sorted (a:int list) <=>
    !i j:int.
      (&0:int) <= i /\ i <= j /\ j < (&(LENGTH a):int)
      ==> odd_even_sort_nth a i <= odd_even_sort_nth a j`;;

let odd_even_sort_odd = new_definition
 `odd_even_sort_odd (i:int) <=> ?k:int. i = (&2:int) * k + (&1:int)`;;

let odd_even_sort_even = new_definition
 `odd_even_sort_even (i:int) <=> ?k:int. i = (&2:int) * k`;;

let odd_even_sort_array_max =
  new_recursive_definition list_RECURSION
   `(odd_even_sort_array_max [] = (&0:int)) /\
    (!h:int. !t:int list.
       odd_even_sort_array_max (CONS h t) =
       if t = [] then h
       else if odd_even_sort_array_max t < h
            then h
            else odd_even_sort_array_max t)`;;

let odd_even_sort_entropy_from =
  new_recursive_definition list_RECURSION
   `(!m k:int.
       odd_even_sort_entropy_from [] m k = (&0:int)) /\
    (!x:int. !xs:int list. !m k:int.
       odd_even_sort_entropy_from (CONS x xs) m k =
       k * (m - x) +
       odd_even_sort_entropy_from xs m (k + (&1:int)))`;;

let odd_even_sort_entropy = new_definition
 `odd_even_sort_entropy (a:int list) (m:int) =
    odd_even_sort_entropy_from a m (&0:int)`;;

let statement =
 `!a:int list.
    (&0:int) < (&(LENGTH a):int)
    ==>
    let m = odd_even_sort_array_max a in
    (!j:int.
       (&0:int) <= j /\ j < (&(LENGTH a):int)
       ==> odd_even_sort_nth a j <= m)
    ==>
    odd_even_sort_permut a a /\
    (!ok:bool. !a1:int list.
       LENGTH a1 = LENGTH a
       ==>
       odd_even_sort_permut a a1 /\
       (ok = T ==> odd_even_sort_sorted a1)
       ==>
       if ~(ok = T) then
         (odd_even_sort_permut a a1 /\
          ((&0:int) <= (&1:int) /\
           (&1:int) <= (&(LENGTH a1):int)) /\
          odd_even_sort_odd (&1:int) /\
          (!j:int.
             (&0:int) <= j /\ j < (&1:int)
             ==> odd_even_sort_odd j
             ==> odd_even_sort_nth a1 j <=
                 odd_even_sort_nth a1 (j + (&1:int))) /\
          (~T ==>
           odd_even_sort_entropy a1 m <
           odd_even_sort_entropy a1 m)) /\
         (!i:int. !ok1:bool. !a2:int list.
            LENGTH a2 = LENGTH a1
            ==>
            odd_even_sort_permut a a2 /\
            ((&0:int) <= i /\ i <= (&(LENGTH a2):int)) /\
            odd_even_sort_odd i /\
            (ok1 = T ==>
             odd_even_sort_entropy a2 m =
             odd_even_sort_entropy a1 m) /\
            (ok1 = T ==>
             (!j:int.
                (&0:int) <= j /\ j < i
                ==> odd_even_sort_odd j
                ==> odd_even_sort_nth a2 j <=
                    odd_even_sort_nth a2 (j + (&1:int)))) /\
            (~(ok1 = T) ==>
             odd_even_sort_entropy a2 m <
             odd_even_sort_entropy a1 m)
            ==>
            if i < (&(LENGTH a2):int) - (&1:int) then
              let o1 = i + (&1:int) in
              ((&0:int) <= o1 /\ o1 < (&(LENGTH a2):int)) /\
              ((&0:int) <= i /\ i < (&(LENGTH a2):int)) /\
              (if odd_even_sort_nth a2 o1 <
                  odd_even_sort_nth a2 i then
                 let o2 = i + (&1:int) in
                 (odd_even_sort_nth a2 o2 <
                    odd_even_sort_nth a2 i /\
                  (&0:int) <= i /\ i < o2 /\
                  o2 < (&(LENGTH a2):int)) /\
                 (!a3:int list.
                    LENGTH a3 = LENGTH a2
                    ==>
                    odd_even_sort_exchange a2 a3 i o2 /\
                    odd_even_sort_entropy a3 m <
                    odd_even_sort_entropy a2 m
                    ==>
                    ((&0:int) <= (&(LENGTH a2):int) - i /\
                     (&(LENGTH a3):int) - (i + (&2:int)) <
                     (&(LENGTH a2):int) - i) /\
                    odd_even_sort_permut a a3 /\
                    ((&0:int) <= i + (&2:int) /\
                     i + (&2:int) <= (&(LENGTH a3):int)) /\
                    odd_even_sort_odd (i + (&2:int)) /\
                    (F = T ==>
                     odd_even_sort_entropy a3 m =
                     odd_even_sort_entropy a1 m) /\
                    (F = T ==>
                     (!j:int.
                        (&0:int) <= j /\ j < i + (&2:int)
                        ==> odd_even_sort_odd j
                        ==> odd_even_sort_nth a3 j <=
                            odd_even_sort_nth
                              a3 (j + (&1:int)))) /\
                    (~(F = T) ==>
                     odd_even_sort_entropy a3 m <
                     odd_even_sort_entropy a1 m))
               else
                 ((&0:int) <= (&(LENGTH a2):int) - i /\
                  (&(LENGTH a2):int) - (i + (&2:int)) <
                  (&(LENGTH a2):int) - i) /\
                 odd_even_sort_permut a a2 /\
                 ((&0:int) <= i + (&2:int) /\
                  i + (&2:int) <= (&(LENGTH a2):int)) /\
                 odd_even_sort_odd (i + (&2:int)) /\
                 (ok1 = T ==>
                  odd_even_sort_entropy a2 m =
                  odd_even_sort_entropy a1 m) /\
                 (ok1 = T ==>
                  (!j:int.
                     (&0:int) <= j /\ j < i + (&2:int)
                     ==> odd_even_sort_odd j
                     ==> odd_even_sort_nth a2 j <=
                         odd_even_sort_nth a2 (j + (&1:int)))) /\
                 (~(ok1 = T) ==>
                  odd_even_sort_entropy a2 m <
                  odd_even_sort_entropy a1 m))
            else
              (odd_even_sort_permut a a2 /\
               ((&0:int) <= (&0:int) /\
                (&0:int) <= (&(LENGTH a2):int)) /\
               odd_even_sort_even (&0:int) /\
               (ok1 = T ==>
                odd_even_sort_entropy a2 m =
                odd_even_sort_entropy a1 m) /\
               (ok1 = T ==>
                (!j:int.
                   ((&0:int) <= j /\
                    j < (&(LENGTH a2):int) - (&1:int)) /\
                   odd_even_sort_odd j
                   ==> odd_even_sort_nth a2 j <=
                       odd_even_sort_nth a2 (j + (&1:int)))) /\
               (ok1 = T ==>
                (!j:int.
                   ((&0:int) <= j /\ j < (&0:int)) /\
                   odd_even_sort_even j
                   ==> odd_even_sort_nth a2 j <=
                       odd_even_sort_nth a2 (j + (&1:int)))) /\
               (~(ok1 = T) ==>
                odd_even_sort_entropy a2 m <
                odd_even_sort_entropy a1 m)) /\
              (!i1:int. !ok2:bool. !a3:int list.
                 LENGTH a3 = LENGTH a2
                 ==>
                 odd_even_sort_permut a a3 /\
                 ((&0:int) <= i1 /\
                  i1 <= (&(LENGTH a3):int)) /\
                 odd_even_sort_even i1 /\
                 (ok2 = T ==>
                  odd_even_sort_entropy a3 m =
                  odd_even_sort_entropy a1 m) /\
                 (ok2 = T ==>
                  (!j:int.
                     ((&0:int) <= j /\
                      j < (&(LENGTH a3):int) - (&1:int)) /\
                     odd_even_sort_odd j
                     ==> odd_even_sort_nth a3 j <=
                         odd_even_sort_nth a3 (j + (&1:int)))) /\
                 (ok2 = T ==>
                  (!j:int.
                     ((&0:int) <= j /\ j < i1) /\
                     odd_even_sort_even j
                     ==> odd_even_sort_nth a3 j <=
                         odd_even_sort_nth a3 (j + (&1:int)))) /\
                 (~(ok2 = T) ==>
                  odd_even_sort_entropy a3 m <
                  odd_even_sort_entropy a1 m)
                 ==>
                 if i1 < (&(LENGTH a3):int) - (&1:int) then
                   let o1 = i1 + (&1:int) in
                   ((&0:int) <= o1 /\
                    o1 < (&(LENGTH a3):int)) /\
                   ((&0:int) <= i1 /\
                    i1 < (&(LENGTH a3):int)) /\
                   (if odd_even_sort_nth a3 o1 <
                       odd_even_sort_nth a3 i1 then
                      let o2 = i1 + (&1:int) in
                      (odd_even_sort_nth a3 o2 <
                         odd_even_sort_nth a3 i1 /\
                       (&0:int) <= i1 /\ i1 < o2 /\
                       o2 < (&(LENGTH a3):int)) /\
                      (!a4:int list.
                         LENGTH a4 = LENGTH a3
                         ==>
                         odd_even_sort_exchange a3 a4 i1 o2 /\
                         odd_even_sort_entropy a4 m <
                         odd_even_sort_entropy a3 m
                         ==>
                         ((&0:int) <=
                            (&(LENGTH a3):int) - i1 /\
                          (&(LENGTH a4):int) -
                            (i1 + (&2:int)) <
                          (&(LENGTH a3):int) - i1) /\
                         odd_even_sort_permut a a4 /\
                         ((&0:int) <= i1 + (&2:int) /\
                          i1 + (&2:int) <=
                            (&(LENGTH a4):int)) /\
                         odd_even_sort_even (i1 + (&2:int)) /\
                         (F = T ==>
                          odd_even_sort_entropy a4 m =
                          odd_even_sort_entropy a1 m) /\
                         (F = T ==>
                          (!j:int.
                             ((&0:int) <= j /\
                              j < (&(LENGTH a4):int) -
                                  (&1:int)) /\
                             odd_even_sort_odd j
                             ==> odd_even_sort_nth a4 j <=
                                 odd_even_sort_nth
                                   a4 (j + (&1:int)))) /\
                         (F = T ==>
                          (!j:int.
                             ((&0:int) <= j /\
                              j < i1 + (&2:int)) /\
                             odd_even_sort_even j
                             ==> odd_even_sort_nth a4 j <=
                                 odd_even_sort_nth
                                   a4 (j + (&1:int)))) /\
                         (~(F = T) ==>
                          odd_even_sort_entropy a4 m <
                          odd_even_sort_entropy a1 m))
                    else
                      ((&0:int) <=
                         (&(LENGTH a3):int) - i1 /\
                       (&(LENGTH a3):int) - (i1 + (&2:int)) <
                         (&(LENGTH a3):int) - i1) /\
                      odd_even_sort_permut a a3 /\
                      ((&0:int) <= i1 + (&2:int) /\
                       i1 + (&2:int) <= (&(LENGTH a3):int)) /\
                      odd_even_sort_even (i1 + (&2:int)) /\
                      (ok2 = T ==>
                       odd_even_sort_entropy a3 m =
                       odd_even_sort_entropy a1 m) /\
                      (ok2 = T ==>
                       (!j:int.
                          ((&0:int) <= j /\
                           j < (&(LENGTH a3):int) - (&1:int)) /\
                          odd_even_sort_odd j
                          ==> odd_even_sort_nth a3 j <=
                              odd_even_sort_nth
                                a3 (j + (&1:int)))) /\
                      (ok2 = T ==>
                       (!j:int.
                          ((&0:int) <= j /\
                           j < i1 + (&2:int)) /\
                          odd_even_sort_even j
                          ==> odd_even_sort_nth a3 j <=
                              odd_even_sort_nth
                                a3 (j + (&1:int)))) /\
                      (~(ok2 = T) ==>
                       odd_even_sort_entropy a3 m <
                       odd_even_sort_entropy a1 m))
                 else
                   ((&0:int) <=
                      odd_even_sort_entropy a1 m +
                      (if ok = T then (&0:int) else (&1:int)) /\
                    odd_even_sort_entropy a3 m +
                      (if ok2 = T then (&0:int) else (&1:int)) <
                    odd_even_sort_entropy a1 m +
                      (if ok = T then (&0:int) else (&1:int))) /\
                   odd_even_sort_permut a a3 /\
                   (ok2 = T ==> odd_even_sort_sorted a3)))
       else
         odd_even_sort_sorted a1 /\
         odd_even_sort_permut a a1)`;;
