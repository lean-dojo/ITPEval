(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/counting_sort_InPlaceCountingSort_in_place_counting_sortqtvc:
  an in-place counting-sort verification condition covering construction of
  value counts, placement-loop invariants, sortedness, and preservation of
  value multiplicities. This file contains no proof.
*)

let counting_sort_nth = new_definition
 `counting_sort_nth (a:int list) (i:int) =
    if i < (&0:int) then
      if a = [] then (&0:int) else EL 0 a
    else if num_of_int i < LENGTH a then
      EL (num_of_int i) a
    else (&0:int)`;;

let counting_sort_update = new_recursive_definition list_RECURSION
 `(!n x.
     counting_sort_update ([]:int list) n x = []) /\
  (!h t n x.
     counting_sort_update (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (counting_sort_update t (PRE n) x))`;;

let counting_sort_numeq = new_definition
 `counting_sort_numeq (a:int list) (v:int) (i:int) (j:int) =
    (&(CARD {n:int |
        i <= n /\ n < j /\ counting_sort_nth a n = v}):int)`;;

let counting_sort_numlt = new_definition
 `counting_sort_numlt (a:int list) (v:int) (i:int) (j:int) =
    (&(CARD {n:int |
        i <= n /\ n < j /\ counting_sort_nth a n < v}):int)`;;

let counting_sort_sorted_sub = new_definition
 `counting_sort_sorted_sub (a:int list) (l:int) (u:int) <=>
    !i1 i2:int.
      l <= i1 /\ i1 <= i2 /\ i2 < u
      ==> counting_sort_nth a i1 <= counting_sort_nth a i2`;;

let counting_sort_sorted = new_definition
 `counting_sort_sorted (a:int list) <=>
    counting_sort_sorted_sub a (&0:int) (&(LENGTH a):int)`;;

let counting_sort_k_values = new_definition
 `counting_sort_k_values (k:int) (a:int list) <=>
    !i:int.
      (&0:int) <= i /\ i < (&(LENGTH a):int)
      ==> (&0:int) <= counting_sort_nth a i /\
          counting_sort_nth a i < k`;;

let counting_sort_permut = new_definition
 `counting_sort_permut (k:int) (a:int list) (b:int list) <=>
    LENGTH a = LENGTH b /\
    (!v:int.
       (&0:int) <= v /\ v < k
       ==> counting_sort_numeq a v (&0:int) (&(LENGTH a):int) =
           counting_sort_numeq b v (&0:int) (&(LENGTH b):int))`;;

let statement =
 `!k:int. !a:int list.
    (&0:int) < k
    ==>
    counting_sort_k_values k a
    ==>
    let finish =
      \(counts:int list).
        let o3 = k - (&1:int) in
        (((&0:int) <= o3 + (&1:int)
          ==>
          ((&0:int) =
             counting_sort_numlt
               a (&0:int) (&0:int) (&(LENGTH a):int) /\
           counting_sort_sorted_sub a (&0:int) (&0:int) /\
           (!e:int.
              (&0:int) <= e /\ e < (&0:int)
              ==> (&0:int) <= counting_sort_nth a e /\
                  counting_sort_nth a e < (&0:int)) /\
           (!f:int.
              (&0:int) <= f /\ f < (&0:int)
              ==> counting_sort_numeq
                    a f (&0:int) (&0:int) =
                  counting_sort_numeq
                    a f (&0:int) (&(LENGTH a):int)) /\
           (!j:int. !a1:int list.
              LENGTH a1 = LENGTH a
              ==>
              ((!v:int.
                  (((&0:int) <= v /\ v <= o3) /\
                   j =
                     counting_sort_numlt
                       a v (&0:int) (&(LENGTH a1):int) /\
                   counting_sort_sorted_sub a1 (&0:int) j /\
                   (!e:int.
                      (&0:int) <= e /\ e < j
                      ==> (&0:int) <= counting_sort_nth a1 e /\
                          counting_sort_nth a1 e < v) /\
                   (!f:int.
                      (&0:int) <= f /\ f < v
                      ==> counting_sort_numeq
                            a1 f (&0:int) j =
                          counting_sort_numeq
                            a f (&0:int) (&(LENGTH a1):int)))
                  ==>
                  ((&0:int) <= v /\ v < (&(LENGTH counts):int)) /\
                  (let o4 = counting_sort_nth counts v in
                   (((&1:int) <= o4 + (&1:int)
                     ==>
                     (j - (&1:int) + (&1:int) =
                        counting_sort_numlt
                          a v (&0:int) (&(LENGTH a1):int) /\
                      counting_sort_sorted_sub a1 (&0:int) j /\
                      (!e:int.
                         (&0:int) <= e /\ e < j
                         ==> (&0:int) <= counting_sort_nth a1 e /\
                             counting_sort_nth a1 e <= v) /\
                      (!f:int.
                         (&0:int) <= f /\ f < v
                         ==> counting_sort_numeq
                               a1 f (&0:int) j =
                             counting_sort_numeq
                               a f (&0:int) (&(LENGTH a1):int)) /\
                      counting_sort_numeq a1 v (&0:int) j =
                        (&1:int) - (&1:int)) /\
                     (!j1:int. !a2:int list.
                        LENGTH a2 = LENGTH a1
                        ==>
                        ((!i:int.
                            (((&1:int) <= i /\ i <= o4) /\
                             j1 - i + (&1:int) =
                               counting_sort_numlt
                                 a v (&0:int) (&(LENGTH a2):int) /\
                             counting_sort_sorted_sub
                               a2 (&0:int) j1 /\
                             (!e:int.
                                (&0:int) <= e /\ e < j1
                                ==> (&0:int) <=
                                      counting_sort_nth a2 e /\
                                    counting_sort_nth a2 e <= v) /\
                             (!f:int.
                                (&0:int) <= f /\ f < v
                                ==> counting_sort_numeq
                                      a2 f (&0:int) j1 =
                                    counting_sort_numeq
                                      a f (&0:int)
                                        (&(LENGTH a2):int)) /\
                             counting_sort_numeq
                               a2 v (&0:int) j1 =
                               i - (&1:int))
                            ==>
                            ((&0:int) <= j1 /\
                             j1 < (&(LENGTH a2):int)) /\
                             (LENGTH
                               (counting_sort_update
                                  a2 (num_of_int j1) v) =
                               LENGTH a2
                             ==>
                             j1 + (&1:int) -
                                 (i + (&1:int)) + (&1:int) =
                               counting_sort_numlt
                                 a v (&0:int)
                                   (&(LENGTH
                                      (counting_sort_update
                                         a2 (num_of_int j1) v)):int) /\
                             counting_sort_sorted_sub
                               (counting_sort_update
                                  a2 (num_of_int j1) v)
                               (&0:int) (j1 + (&1:int)) /\
                             (!e:int.
                                (&0:int) <= e /\
                                e < j1 + (&1:int)
                                ==> (&0:int) <=
                                      counting_sort_nth
                                        (counting_sort_update
                                           a2 (num_of_int j1) v) e /\
                                    counting_sort_nth
                                      (counting_sort_update
                                         a2 (num_of_int j1) v) e <= v) /\
                             (!f:int.
                                (&0:int) <= f /\ f < v
                                ==> counting_sort_numeq
                                      (counting_sort_update
                                         a2 (num_of_int j1) v)
                                      f (&0:int) (j1 + (&1:int)) =
                                    counting_sort_numeq
                                      a f (&0:int)
                                        (&(LENGTH
                                           (counting_sort_update
                                              a2 (num_of_int j1) v)):int)) /\
                             counting_sort_numeq
                               (counting_sort_update
                                  a2 (num_of_int j1) v)
                               v (&0:int) (j1 + (&1:int)) =
                               i + (&1:int) - (&1:int))) /\
                         ((j1 - (o4 + (&1:int)) + (&1:int) =
                             counting_sort_numlt
                               a v (&0:int) (&(LENGTH a2):int) /\
                           counting_sort_sorted_sub a2 (&0:int) j1 /\
                           (!e:int.
                              (&0:int) <= e /\ e < j1
                              ==> (&0:int) <= counting_sort_nth a2 e /\
                                  counting_sort_nth a2 e <= v) /\
                           (!f:int.
                              (&0:int) <= f /\ f < v
                              ==> counting_sort_numeq
                                    a2 f (&0:int) j1 =
                                  counting_sort_numeq
                                    a f (&0:int) (&(LENGTH a2):int)) /\
                           counting_sort_numeq a2 v (&0:int) j1 =
                             o4 + (&1:int) - (&1:int))
                          ==>
                          j1 =
                            counting_sort_numlt
                              a (v + (&1:int)) (&0:int)
                                (&(LENGTH a2):int) /\
                          counting_sort_sorted_sub a2 (&0:int) j1 /\
                          (!e:int.
                             (&0:int) <= e /\ e < j1
                             ==> (&0:int) <= counting_sort_nth a2 e /\
                                 counting_sort_nth a2 e <
                                   v + (&1:int)) /\
                          (!f:int.
                             (&0:int) <= f /\ f < v + (&1:int)
                             ==> counting_sort_numeq
                                   a2 f (&0:int) j1 =
                                 counting_sort_numeq
                                   a f (&0:int) (&(LENGTH a2):int)))))
                    /\
                    (o4 + (&1:int) < (&1:int)
                     ==>
                     j =
                       counting_sort_numlt
                         a (v + (&1:int)) (&0:int)
                           (&(LENGTH a1):int) /\
                     counting_sort_sorted_sub a1 (&0:int) j /\
                     (!e:int.
                        (&0:int) <= e /\ e < j
                        ==> (&0:int) <= counting_sort_nth a1 e /\
                            counting_sort_nth a1 e < v + (&1:int)) /\
                     (!f:int.
                        (&0:int) <= f /\ f < v + (&1:int)
                        ==> counting_sort_numeq
                              a1 f (&0:int) j =
                            counting_sort_numeq
                              a f (&0:int) (&(LENGTH a1):int)))))))
               /\
               ((j =
                   counting_sort_numlt
                     a (o3 + (&1:int)) (&0:int)
                       (&(LENGTH a1):int) /\
                 counting_sort_sorted_sub a1 (&0:int) j /\
                 (!e:int.
                    (&0:int) <= e /\ e < j
                    ==> (&0:int) <= counting_sort_nth a1 e /\
                        counting_sort_nth a1 e < o3 + (&1:int)) /\
                 (!f:int.
                    (&0:int) <= f /\ f < o3 + (&1:int)
                    ==> counting_sort_numeq
                          a1 f (&0:int) j =
                        counting_sort_numeq
                          a f (&0:int) (&(LENGTH a1):int)))
                ==>
                counting_sort_sorted a1 /\
                counting_sort_permut k a a1))))
         /\
         (o3 + (&1:int) < (&0:int)
          ==>
          counting_sort_sorted a /\
          counting_sort_permut k a a))) in
    (&0:int) <= k /\
    (!c:int list.
       ((!i:int.
           (&0:int) <= i /\ i < k
           ==> counting_sort_nth c i = (&0:int)) /\
        (&(LENGTH c):int) = k)
       ==>
       (let o2 = (&(LENGTH a):int) - (&1:int) in
        (((&0:int) <= o2 + (&1:int)
          ==>
          (!v:int.
             (&0:int) <= v /\ v < k
             ==> counting_sort_nth c v =
                 counting_sort_numeq
                   a v (&0:int) (&0:int)) /\
          (!c1:int list.
             LENGTH c1 = LENGTH c
             ==>
             ((!i:int.
                 (((&0:int) <= i /\ i <= o2) /\
                  (!v:int.
                     (&0:int) <= v /\ v < k
                     ==> counting_sort_nth c1 v =
                         counting_sort_numeq
                           a v (&0:int) i))
                 ==>
                 ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
                 (let v = counting_sort_nth a i in
                  ((&0:int) <= v /\ v < (&(LENGTH c1):int)) /\
                  (let o3 =
                     counting_sort_nth c1 v + (&1:int) in
                   ((&0:int) <= v /\ v < (&(LENGTH c1):int)) /\
                   (LENGTH
                      (counting_sort_update
                         c1 (num_of_int v) o3) =
                      LENGTH c1
                    ==>
                    (!v1:int.
                       (&0:int) <= v1 /\ v1 < k
                       ==> counting_sort_nth
                             (counting_sort_update
                                c1 (num_of_int v) o3) v1 =
                           counting_sort_numeq
                             a v1 (&0:int) (i + (&1:int))))))) /\
              ((!v:int.
                  (&0:int) <= v /\ v < k
                  ==> counting_sort_nth c1 v =
                      counting_sort_numeq
                        a v (&0:int) (o2 + (&1:int)))
               ==>
               finish c1))))
         /\
         (o2 + (&1:int) < (&0:int)
          ==>
          finish c))))`;;
