(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/kmp_KnuthMorrisPratt_kmpqtvc: the Knuth-Morris-Pratt search
  verification condition, preserving prefix-match and first-occurrence
  invariants while using a maximal-border next table. This file contains no
  proof.
*)

ignore (new_definition
 `kmpqtvc_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`);;

ignore (new_definition
 `kmpqtvc_nth_char (a:A list) (i:int) =
    if kmpqtvc_to_num i < LENGTH a
    then EL (kmpqtvc_to_num i) a
    else ARB`);;

ignore (new_definition
 `kmpqtvc_nth_int (a:int list) (i:int) =
    if kmpqtvc_to_num i < LENGTH a
    then EL (kmpqtvc_to_num i) a
    else (&0:int)`);;

ignore (new_definition
 `kmpqtvc_matches1
    (a1:A list) (i1:int) (a2:A list) (i2:int) (n:int) <=>
    (((&0:int) <= i1 /\ i1 <= (&(LENGTH a1):int) - n) /\
     ((&0:int) <= i2 /\ i2 <= (&(LENGTH a2):int) - n) /\
     (!i:int.
        (&0:int) <= i /\ i < n
        ==> kmpqtvc_nth_char a1 (i1 + i) =
            kmpqtvc_nth_char a2 (i2 + i)))`);;

ignore (new_definition
 `kmpqtvc_is_next (p:A list) (j:int) (n:int) <=>
    ((&0:int) <= n /\ n < j) /\
    kmpqtvc_matches1 p (j - n) p (&0:int) n /\
    (!z:int.
       n < z /\ z < j
       ==> ~kmpqtvc_matches1 p (j - z) p (&0:int) z)`);;

ignore (new_definition
 `kmpqtvc_first_occur (p:A list) (a:A list) (r:int) <=>
    (((&0:int) <= r /\ r < (&(LENGTH a):int)
      ==> kmpqtvc_matches1
            a r p (&0:int) (&(LENGTH p):int)) /\
     (!k:int.
        (&0:int) <= k /\ k < r
        ==> ~kmpqtvc_matches1
              a k p (&0:int) (&(LENGTH p):int)))`);;

ignore
 `!p a:A list.
    (&1:int) <= (&(LENGTH p):int)
    ==>
    let m = (&(LENGTH p):int) in
    let n = (&(LENGTH a):int) in
    (&1:int) <= (&(LENGTH p):int) /\
    (!next:int list.
       LENGTH next = LENGTH p /\
       (!j:int.
          (&0:int) < j /\ j < (&(LENGTH p):int)
          ==> kmpqtvc_is_next p j (kmpqtvc_nth_int next j))
       ==>
       ((((&0:int) <= (&0:int) /\ (&0:int) <= m) /\
         ((&0:int) <= (&0:int) /\ (&0:int) <= n)) /\
        kmpqtvc_matches1
          a ((&0:int) - (&0:int)) p (&0:int) (&0:int) /\
        (!k:int.
           (&0:int) <= k /\ k < (&0:int) - (&0:int)
           ==> ~kmpqtvc_matches1 a k p (&0:int) m)) /\
       (!j i:int.
          ((((&0:int) <= j /\ j <= m) /\ j <= i /\ i <= n) /\
           kmpqtvc_matches1 a (i - j) p (&0:int) j /\
           (!k:int.
              (&0:int) <= k /\ k < i - j
              ==> ~kmpqtvc_matches1 a k p (&0:int) m))
          ==>
          (!o1:bool.
             (if j < m
              then o1 = (if i < n then T else F)
              else o1 = F)
             ==>
             (if o1 = T then
                ((&0:int) <= j /\ j < (&(LENGTH p):int)) /\
                ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
                (if kmpqtvc_nth_char a i =
                    kmpqtvc_nth_char p j then
                   (((&0:int) <= n - i /\
                     n - (i + (&1:int)) < n - i) \/
                    (n - i = n - (i + (&1:int)) /\
                     (&0:int) <= j /\
                     j + (&1:int) < j)) /\
                   (((&0:int) <= j + (&1:int) /\
                     j + (&1:int) <= m) /\
                    j + (&1:int) <= i + (&1:int) /\
                    i + (&1:int) <= n) /\
                   kmpqtvc_matches1
                     a (i + (&1:int) - (j + (&1:int)))
                     p (&0:int) (j + (&1:int)) /\
                   (!k:int.
                      (&0:int) <= k /\
                      k < i + (&1:int) - (j + (&1:int))
                      ==> ~kmpqtvc_matches1
                            a k p (&0:int) m)
                 else if j = (&0:int) then
                   (((&0:int) <= n - i /\
                     n - (i + (&1:int)) < n - i) \/
                    (n - i = n - (i + (&1:int)) /\
                     (&0:int) <= j /\
                     j < j)) /\
                   (((&0:int) <= j /\ j <= m) /\
                    j <= i + (&1:int) /\
                    i + (&1:int) <= n) /\
                   kmpqtvc_matches1
                     a (i + (&1:int) - j) p (&0:int) j /\
                   (!k:int.
                      (&0:int) <= k /\ k < i + (&1:int) - j
                      ==> ~kmpqtvc_matches1
                            a k p (&0:int) m)
                 else
                   ((&0:int) <= j /\
                    j < (&(LENGTH next):int)) /\
                   (((&0:int) <= n - i /\ n - i < n - i) \/
                    ((&0:int) <= j /\
                     kmpqtvc_nth_int next j < j)) /\
                   (((&0:int) <= kmpqtvc_nth_int next j /\
                     kmpqtvc_nth_int next j <= m) /\
                    kmpqtvc_nth_int next j <= i /\
                    i <= n) /\
                   kmpqtvc_matches1
                     a (i - kmpqtvc_nth_int next j)
                     p (&0:int) (kmpqtvc_nth_int next j) /\
                   (!k:int.
                      (&0:int) <= k /\
                      k < i - kmpqtvc_nth_int next j
                      ==> ~kmpqtvc_matches1
                            a k p (&0:int) m))
              else
                !result:int.
                  (if j = m then result = i - m else result = i)
                  ==> kmpqtvc_first_occur p a result))))`;;
