(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2017_odd_even_transposition_sort_Challenge3_odd_even_transposition_sortqtvc:
  the verification condition for sequential odd-even transposition sorting of
  an integer array, including permutation, parity-indexed ordering invariants,
  adjacent swaps, inversion-count variants, and final sortedness. This file
  contains no proof.
*)

let odd_even_transposition_to_num = new_definition
 `odd_even_transposition_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let odd_even_transposition_nth = new_definition
 `odd_even_transposition_nth (a:int list) (i:int) =
    if odd_even_transposition_to_num i < LENGTH a
    then EL (odd_even_transposition_to_num i) a
    else (&0:int)`;;

let odd_even_transposition_update =
  new_recursive_definition list_RECURSION
   `(!n:num. !x:int.
       odd_even_transposition_update [] n x = []) /\
    (!h:int. !t:int list. !n:num. !x:int.
       odd_even_transposition_update (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (odd_even_transposition_update t (PRE n) x))`;;

let odd_even_transposition_exchange = new_definition
 `odd_even_transposition_exchange
    (before:int list) (after:int list) (i:int) (j:int) <=>
    after =
      odd_even_transposition_update
        (odd_even_transposition_update
          before
          (odd_even_transposition_to_num i)
          (odd_even_transposition_nth before j))
        (odd_even_transposition_to_num j)
        (odd_even_transposition_nth before i)`;;

let odd_even_transposition_permut = new_definition
 `odd_even_transposition_permut (a:int list) (b:int list) <=>
    LENGTH a = LENGTH b /\
    (!v:int.
       CARD {k:num | k < LENGTH a /\ EL k a = v} =
       CARD {k:num | k < LENGTH b /\ EL k b = v})`;;

let odd_even_transposition_sorted = new_definition
 `odd_even_transposition_sorted (a:int list) <=>
    !i j:int.
      (&0:int) <= i /\ i <= j /\ j < (&(LENGTH a):int)
      ==> odd_even_transposition_nth a i <=
          odd_even_transposition_nth a j`;;

let odd_even_transposition_odd_sorted = new_definition
 `odd_even_transposition_odd_sorted (a:int list) (n:int) <=>
    !i:int.
      (&0:int) <= i
      ==> (&2:int) * i + (&2:int) < n
      ==> odd_even_transposition_nth
            a ((&2:int) * i + (&1:int)) <=
          odd_even_transposition_nth
            a ((&2:int) * i + (&2:int))`;;

let odd_even_transposition_even_sorted = new_definition
 `odd_even_transposition_even_sorted (a:int list) (n:int) <=>
    !i:int.
      (&0:int) <= i
      ==> (&2:int) * i + (&1:int) < n
      ==> odd_even_transposition_nth a ((&2:int) * i) <=
          odd_even_transposition_nth
            a ((&2:int) * i + (&1:int))`;;

let odd_even_transposition_inversions = new_definition
 `odd_even_transposition_inversions (a:int list) =
    (&(CARD {p:num#num |
        FST p < SND p /\
        SND p < LENGTH a /\
        EL (SND p) a < EL (FST p) a}):int)`;;

let statement =
 `!a:int list.
    odd_even_transposition_permut a a /\
    (!is_sorted:bool. !a1:int list.
       LENGTH a1 = LENGTH a
       ==>
       odd_even_transposition_permut a a1 /\
       (is_sorted = T ==> odd_even_transposition_sorted a1)
       ==>
       if ~(is_sorted = T) then
         (((&0:int) <= (&0:int) /\
           (&0:int) <= (&1:int) /\
           (&1:int) = (&2:int) * (&0:int) + (&1:int)) /\
          odd_even_transposition_permut a a1 /\
          odd_even_transposition_odd_sorted a1 (&1:int) /\
          (~T ==>
           odd_even_transposition_inversions a1 <
           odd_even_transposition_inversions a1)) /\
         (!half_i:int. !is_sorted1:bool. !a2:int list.
            LENGTH a2 = LENGTH a1
            ==>
            (((&0:int) <= half_i /\
              (&0:int) <= (&2:int) * half_i + (&1:int)) /\
             odd_even_transposition_permut a a2 /\
             odd_even_transposition_odd_sorted
               a2 ((&2:int) * half_i + (&1:int)) /\
             (if is_sorted1 = T then
                odd_even_transposition_inversions a2 =
                odd_even_transposition_inversions a1
              else
                odd_even_transposition_inversions a2 <
                odd_even_transposition_inversions a1))
            ==>
            if (&2:int) * half_i + (&1:int) <
               (&(LENGTH a2):int) - (&1:int) then
              let o1 =
                (&2:int) * half_i + (&1:int) + (&1:int) in
              ((&0:int) <= o1 /\ o1 < (&(LENGTH a2):int)) /\
              ((&0:int) <= (&2:int) * half_i + (&1:int) /\
               (&2:int) * half_i + (&1:int) <
               (&(LENGTH a2):int)) /\
              (if odd_even_transposition_nth a2 o1 <
                  odd_even_transposition_nth
                    a2 ((&2:int) * half_i + (&1:int)) then
                 let o2 =
                   (&2:int) * half_i + (&1:int) + (&1:int) in
                 (((&0:int) <= (&2:int) * half_i + (&1:int) /\
                   (&2:int) * half_i + (&1:int) <
                   (&(LENGTH a2):int)) /\
                  (&0:int) <= o2 /\ o2 < (&(LENGTH a2):int)) /\
                 (!a3:int list.
                    LENGTH a3 = LENGTH a2
                    ==>
                    odd_even_transposition_exchange
                      a2 a3 ((&2:int) * half_i + (&1:int)) o2
                    ==>
                    ((&0:int) <=
                       (&(LENGTH a2):int) -
                       ((&2:int) * half_i + (&1:int)) /\
                     (&(LENGTH a3):int) -
                       ((&2:int) * half_i + (&1:int) + (&2:int)) <
                     (&(LENGTH a2):int) -
                       ((&2:int) * half_i + (&1:int))) /\
                    ((&0:int) <= half_i + (&1:int) /\
                     (&0:int) <=
                       (&2:int) * half_i + (&1:int) + (&2:int) /\
                     (&2:int) * half_i + (&1:int) + (&2:int) =
                       (&2:int) * (half_i + (&1:int)) + (&1:int)) /\
                    odd_even_transposition_permut a a3 /\
                    odd_even_transposition_odd_sorted
                      a3
                      ((&2:int) * half_i + (&1:int) + (&2:int)) /\
                    (if F = T then
                       odd_even_transposition_inversions a3 =
                       odd_even_transposition_inversions a1
                     else
                       odd_even_transposition_inversions a3 <
                       odd_even_transposition_inversions a1))
               else
                 ((&0:int) <=
                    (&(LENGTH a2):int) -
                    ((&2:int) * half_i + (&1:int)) /\
                  (&(LENGTH a2):int) -
                    ((&2:int) * half_i + (&1:int) + (&2:int)) <
                  (&(LENGTH a2):int) -
                    ((&2:int) * half_i + (&1:int))) /\
                 ((&0:int) <= half_i + (&1:int) /\
                  (&0:int) <=
                    (&2:int) * half_i + (&1:int) + (&2:int) /\
                  (&2:int) * half_i + (&1:int) + (&2:int) =
                    (&2:int) * (half_i + (&1:int)) + (&1:int)) /\
                 odd_even_transposition_permut a a2 /\
                 odd_even_transposition_odd_sorted
                   a2
                   ((&2:int) * half_i + (&1:int) + (&2:int)) /\
                 (if is_sorted1 = T then
                    odd_even_transposition_inversions a2 =
                    odd_even_transposition_inversions a1
                  else
                    odd_even_transposition_inversions a2 <
                    odd_even_transposition_inversions a1))
            else
              (((&0:int) <= (&0:int) /\
                (&0:int) <= (&0:int) /\
                (&0:int) = (&2:int) * (&0:int)) /\
               (&0:int) <= (&0:int) /\
               odd_even_transposition_permut a a2 /\
               (is_sorted1 = T ==>
                odd_even_transposition_odd_sorted
                  a2 (&(LENGTH a2):int)) /\
               odd_even_transposition_even_sorted a2 (&0:int) /\
               (if is_sorted1 = T then
                  odd_even_transposition_inversions a2 =
                  odd_even_transposition_inversions a1
                else
                  odd_even_transposition_inversions a2 <
                  odd_even_transposition_inversions a1) /\
               (is_sorted1 = T \/
                odd_even_transposition_inversions a2 <
                odd_even_transposition_inversions a1)) /\
              (!half_i1:int. !is_sorted2:bool. !a3:int list.
                 LENGTH a3 = LENGTH a2
                 ==>
                 (((&0:int) <= half_i1 /\
                   (&0:int) <= (&2:int) * half_i1) /\
                  (&0:int) <= (&2:int) * half_i1 /\
                  odd_even_transposition_permut a a3 /\
                  (is_sorted2 = T ==>
                   odd_even_transposition_odd_sorted
                     a3 (&(LENGTH a3):int)) /\
                  odd_even_transposition_even_sorted
                    a3 ((&2:int) * half_i1) /\
                  (if is_sorted2 = T then
                     odd_even_transposition_inversions a3 =
                     odd_even_transposition_inversions a1
                   else
                     odd_even_transposition_inversions a3 <
                     odd_even_transposition_inversions a1) /\
                  (is_sorted2 = T \/
                   odd_even_transposition_inversions a3 <
                   odd_even_transposition_inversions a1))
                 ==>
                 if (&2:int) * half_i1 <
                    (&(LENGTH a3):int) - (&1:int) then
                   let o1 =
                     (&2:int) * half_i1 + (&1:int) in
                   ((&0:int) <= o1 /\
                    o1 < (&(LENGTH a3):int)) /\
                   ((&0:int) <= (&2:int) * half_i1 /\
                    (&2:int) * half_i1 < (&(LENGTH a3):int)) /\
                   (if odd_even_transposition_nth a3 o1 <
                       odd_even_transposition_nth
                         a3 ((&2:int) * half_i1) then
                      let o2 =
                        (&2:int) * half_i1 + (&1:int) in
                      (((&0:int) <= (&2:int) * half_i1 /\
                        (&2:int) * half_i1 <
                        (&(LENGTH a3):int)) /\
                       (&0:int) <= o2 /\
                       o2 < (&(LENGTH a3):int)) /\
                      (!a4:int list.
                         LENGTH a4 = LENGTH a3
                         ==>
                         odd_even_transposition_exchange
                           a3 a4 ((&2:int) * half_i1) o2
                         ==>
                         ((&0:int) <=
                            (&(LENGTH a3):int) -
                            (&2:int) * half_i1 /\
                          (&(LENGTH a4):int) -
                            ((&2:int) * half_i1 + (&2:int)) <
                          (&(LENGTH a3):int) -
                            (&2:int) * half_i1) /\
                         ((&0:int) <= half_i1 + (&1:int) /\
                          (&0:int) <=
                            (&2:int) * half_i1 + (&2:int) /\
                          (&2:int) * half_i1 + (&2:int) =
                            (&2:int) * (half_i1 + (&1:int))) /\
                         (&0:int) <=
                           (&2:int) * half_i1 + (&2:int) /\
                         odd_even_transposition_permut a a4 /\
                         (F = T ==>
                          odd_even_transposition_odd_sorted
                            a4 (&(LENGTH a4):int)) /\
                         odd_even_transposition_even_sorted
                           a4
                           ((&2:int) * half_i1 + (&2:int)) /\
                         (if F = T then
                            odd_even_transposition_inversions a4 =
                            odd_even_transposition_inversions a1
                          else
                            odd_even_transposition_inversions a4 <
                            odd_even_transposition_inversions a1) /\
                         (F = T \/
                          odd_even_transposition_inversions a4 <
                          odd_even_transposition_inversions a1))
                    else
                      ((&0:int) <=
                         (&(LENGTH a3):int) -
                         (&2:int) * half_i1 /\
                       (&(LENGTH a3):int) -
                         ((&2:int) * half_i1 + (&2:int)) <
                       (&(LENGTH a3):int) -
                         (&2:int) * half_i1) /\
                      ((&0:int) <= half_i1 + (&1:int) /\
                       (&0:int) <=
                         (&2:int) * half_i1 + (&2:int) /\
                       (&2:int) * half_i1 + (&2:int) =
                         (&2:int) * (half_i1 + (&1:int))) /\
                      (&0:int) <=
                        (&2:int) * half_i1 + (&2:int) /\
                      odd_even_transposition_permut a a3 /\
                      (is_sorted2 = T ==>
                       odd_even_transposition_odd_sorted
                         a3 (&(LENGTH a3):int)) /\
                      odd_even_transposition_even_sorted
                        a3
                        ((&2:int) * half_i1 + (&2:int)) /\
                      (if is_sorted2 = T then
                         odd_even_transposition_inversions a3 =
                         odd_even_transposition_inversions a1
                       else
                         odd_even_transposition_inversions a3 <
                         odd_even_transposition_inversions a1) /\
                      (is_sorted2 = T \/
                       odd_even_transposition_inversions a3 <
                       odd_even_transposition_inversions a1))
                 else
                   (((&0:int) <=
                       (if is_sorted = T
                        then (&0:int) else (&1:int)) /\
                     (if is_sorted2 = T
                      then (&0:int) else (&1:int)) <
                     (if is_sorted = T
                      then (&0:int) else (&1:int))) \/
                    ((if is_sorted = T
                      then (&0:int) else (&1:int)) =
                     (if is_sorted2 = T
                      then (&0:int) else (&1:int)) /\
                     (&0:int) <=
                       odd_even_transposition_inversions a1 /\
                     odd_even_transposition_inversions a3 <
                       odd_even_transposition_inversions a1)) /\
                   odd_even_transposition_permut a a3 /\
                   (is_sorted2 = T ==>
                    odd_even_transposition_sorted a3)))
       else
         odd_even_transposition_sorted a1 /\
         odd_even_transposition_permut a a1)`;;
