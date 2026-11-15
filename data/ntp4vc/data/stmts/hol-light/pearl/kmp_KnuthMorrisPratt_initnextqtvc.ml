(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/kmp_KnuthMorrisPratt_initnextqtvc: the Knuth-Morris-Pratt
  initialization verification condition for constructing the next table
  while preserving prefix-match and maximal-border invariants. This file
  contains no proof.
*)

ignore (new_definition
 `kmp_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`);;

ignore (new_definition
 `kmp_nth_char (a:A list) (i:int) =
    if kmp_to_num i < LENGTH a then EL (kmp_to_num i) a else ARB`);;

ignore (new_definition
 `kmp_nth_int (a:int list) (i:int) =
    if kmp_to_num i < LENGTH a
    then EL (kmp_to_num i) a
    else (&0:int)`);;

ignore (
  new_recursive_definition list_RECURSION
   `(!n x:int. kmp_update_nat [] n x = []) /\
    (!h:int.
     !t:int list.
     !n:num.
     !x:int.
       kmp_update_nat (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (kmp_update_nat t (PRE n) x))`);;

ignore (new_definition
 `kmp_update (a:int list) (i:int) (x:int) =
    kmp_update_nat a (kmp_to_num i) x`);;

ignore (new_definition
 `kmp_matches1
    (a1:A list) (i1:int) (a2:A list) (i2:int) (n:int) <=>
    (((&0:int) <= i1 /\ i1 <= (&(LENGTH a1):int) - n) /\
     ((&0:int) <= i2 /\ i2 <= (&(LENGTH a2):int) - n) /\
     (!i:int.
        (&0:int) <= i /\ i < n
        ==> kmp_nth_char a1 (i1 + i) =
            kmp_nth_char a2 (i2 + i)))`);;

ignore (new_definition
 `kmp_is_next (p:A list) (j:int) (n:int) <=>
    ((&0:int) <= n /\ n < j) /\
    kmp_matches1 p (j - n) p (&0:int) n /\
    (!z:int.
       n < z /\ z < j
       ==> ~kmp_matches1 p (j - z) p (&0:int) z)`);;

ignore
 `!p:A list.
    (&1:int) <= (&(LENGTH p):int)
    ==>
    let m = (&(LENGTH p):int) in
    (&0:int) <= m /\
    (!next:int list.
       (!i:int.
          (&0:int) <= i /\ i < m
          ==> kmp_nth_int next i = (&0:int)) /\
       (&(LENGTH next):int) = m
       ==>
       if (&1:int) < m then
         ((&0:int) <= (&1:int) /\
          (&1:int) < (&(LENGTH next):int)) /\
         (LENGTH (kmp_update next (&1:int) (&0:int)) = LENGTH next
          ==>
          (!r:int.
             kmp_nth_int (kmp_update next (&1:int) (&0:int)) r =
             (if r = (&1:int)
              then (&0:int)
              else kmp_nth_int next r))
          ==>
          ((((&0:int) <= (&0:int) /\
             (&0:int) < (&1:int) /\
             (&1:int) <= m) /\
            kmp_matches1 p ((&1:int) - (&0:int))
              p (&0:int) (&0:int) /\
            (!z:int.
               (&0:int) + (&1:int) < z /\
               z < (&1:int) + (&1:int)
               ==>
               ~kmp_matches1 p
                 ((&1:int) + (&1:int) - z) p (&0:int) z) /\
            (!k:int.
               (&0:int) < k /\ k <= (&1:int)
               ==>
               kmp_is_next p k
                 (kmp_nth_int
                   (kmp_update next (&1:int) (&0:int)) k))) /\
           (!j i:int.
            !next1:int list.
              LENGTH next1 =
                LENGTH (kmp_update next (&1:int) (&0:int))
              ==>
              (((&0:int) <= j /\ j < i /\ i <= m) /\
               kmp_matches1 p (i - j) p (&0:int) j /\
               (!z:int.
                  j + (&1:int) < z /\ z < i + (&1:int)
                  ==>
                  ~kmp_matches1 p
                    (i + (&1:int) - z) p (&0:int) z) /\
               (!k:int.
                  (&0:int) < k /\ k <= i
                  ==> kmp_is_next p k (kmp_nth_int next1 k)))
              ==>
              if i < m - (&1:int) then
                ((&0:int) <= j /\ j < (&(LENGTH p):int)) /\
                ((&0:int) <= i /\ i < (&(LENGTH p):int)) /\
                (if kmp_nth_char p i = kmp_nth_char p j then
                   ((&0:int) <= i + (&1:int) /\
                    i + (&1:int) < (&(LENGTH next1):int)) /\
                   (LENGTH
                      (kmp_update next1
                        (i + (&1:int)) (j + (&1:int))) =
                    LENGTH next1
                    ==>
                    (!r:int.
                       kmp_nth_int
                         (kmp_update next1
                           (i + (&1:int)) (j + (&1:int))) r =
                       (if r = i + (&1:int)
                        then j + (&1:int)
                        else kmp_nth_int next1 r))
                    ==>
                    ((((&0:int) <= m - i /\
                       m - (i + (&1:int)) < m - i) \/
                      (m - i = m - (i + (&1:int)) /\
                       (&0:int) <= j /\
                       j + (&1:int) < j)) /\
                     ((&0:int) <= j + (&1:int) /\
                      j + (&1:int) < i + (&1:int) /\
                      i + (&1:int) <= m) /\
                     kmp_matches1 p
                       (i + (&1:int) - (j + (&1:int)))
                       p (&0:int) (j + (&1:int)) /\
                     (!z:int.
                        j + (&1:int) + (&1:int) < z /\
                        z < i + (&1:int) + (&1:int)
                        ==>
                        ~kmp_matches1 p
                          (i + (&1:int) + (&1:int) - z)
                          p (&0:int) z) /\
                     (!k:int.
                        (&0:int) < k /\ k <= i + (&1:int)
                        ==>
                        kmp_is_next p k
                          (kmp_nth_int
                            (kmp_update next1
                              (i + (&1:int)) (j + (&1:int))) k))))
                 else if j = (&0:int) then
                   ((&0:int) <= i + (&1:int) /\
                    i + (&1:int) < (&(LENGTH next1):int)) /\
                   (LENGTH
                      (kmp_update next1
                        (i + (&1:int)) (&0:int)) =
                    LENGTH next1
                    ==>
                    (!r:int.
                       kmp_nth_int
                         (kmp_update next1
                           (i + (&1:int)) (&0:int)) r =
                       (if r = i + (&1:int)
                        then (&0:int)
                        else kmp_nth_int next1 r))
                    ==>
                    ((((&0:int) <= m - i /\
                       m - (i + (&1:int)) < m - i) \/
                      (m - i = m - (i + (&1:int)) /\
                       (&0:int) <= j /\
                       j < j)) /\
                     ((&0:int) <= j /\
                      j < i + (&1:int) /\
                      i + (&1:int) <= m) /\
                     kmp_matches1 p
                       (i + (&1:int) - j) p (&0:int) j /\
                     (!z:int.
                        j + (&1:int) < z /\
                        z < i + (&1:int) + (&1:int)
                        ==>
                        ~kmp_matches1 p
                          (i + (&1:int) + (&1:int) - z)
                          p (&0:int) z) /\
                     (!k:int.
                        (&0:int) < k /\ k <= i + (&1:int)
                        ==>
                        kmp_is_next p k
                          (kmp_nth_int
                            (kmp_update next1
                              (i + (&1:int)) (&0:int)) k))))
                 else
                   ((&0:int) <= j /\
                    j < (&(LENGTH next1):int)) /\
                   (((&0:int) <= m - i /\ m - i < m - i) \/
                    ((&0:int) <= j /\ kmp_nth_int next1 j < j)) /\
                   ((&0:int) <= kmp_nth_int next1 j /\
                    kmp_nth_int next1 j < i /\
                    i <= m) /\
                   kmp_matches1 p
                     (i - kmp_nth_int next1 j)
                     p (&0:int) (kmp_nth_int next1 j) /\
                   (!z:int.
                      kmp_nth_int next1 j + (&1:int) < z /\
                      z < i + (&1:int)
                      ==>
                      ~kmp_matches1 p
                        (i + (&1:int) - z) p (&0:int) z) /\
                   (!k:int.
                      (&0:int) < k /\ k <= i
                      ==> kmp_is_next p k
                        (kmp_nth_int next1 k)))
              else
                LENGTH next1 = LENGTH p /\
                (!j1:int.
                   (&0:int) < j1 /\ j1 < (&(LENGTH p):int)
                   ==> kmp_is_next p j1
                     (kmp_nth_int next1 j1)))))
       else
         LENGTH next = LENGTH p /\
         (!j:int.
            (&0:int) < j /\ j < (&(LENGTH p):int)
            ==> kmp_is_next p j (kmp_nth_int next j)))`;;
