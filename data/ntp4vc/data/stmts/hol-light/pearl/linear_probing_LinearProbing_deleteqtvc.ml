(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linear_probing_LinearProbing_deleteqtvc: the verification condition
  for deletion from a linear-probing hash table, including cyclic probing,
  relocation of entries, and preservation of the table validity invariant.
  This file contains no proof.
*)

let lp_delete_int_index = new_definition
 `lp_delete_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let lp_delete_nth = new_definition
 `lp_delete_nth (xs:A list) (i:int) =
    if lp_delete_int_index i < LENGTH xs
    then EL (lp_delete_int_index i) xs
    else ARB`;;

let lp_delete_update_nat =
  new_recursive_definition list_RECURSION
   `(!n:num.
     !x:A.
       lp_delete_update_nat [] n x = []) /\
    (!h:A.
     !t:A list.
     !n:num.
     !x:A.
       lp_delete_update_nat (CONS h t) n x =
       if n = 0
       then CONS x t
       else CONS h (lp_delete_update_nat t (PRE n) x))`;;

let lp_delete_update_list = new_definition
 `lp_delete_update_list (xs:A list) (i:int) (x:A) =
    lp_delete_update_nat xs (lp_delete_int_index i) x`;;

let lp_delete_update_function = new_definition
 `lp_delete_update_function (f:A->B) (x:A) (y:B) =
    \z. if z = x then y else f z`;;

let lp_delete_array_function_equal = new_definition
 `lp_delete_array_function_equal
    (xs:A list) (f:int->B) (g:int->B) <=>
    !i:int.
      (&0:int) <= i /\ i < (&(LENGTH xs):int)
      ==> f i = g i`;;

let lp_delete_bucket = new_definition
 `lp_delete_bucket (hash:A->int) (k:A) (n:int) = hash k rem n`;;

let lp_delete_between = new_definition
 `lp_delete_between (l:int) (j:int) (r:int) <=>
    (l <= j /\ j < r) \/
    (r < l /\ l <= j) \/
    (j < r /\ r < l)`;;

let lp_delete_next = new_definition
 `lp_delete_next (n:int) (i:int) =
    let i1 = i + (&1:int) in
    if i1 = n then (&0:int) else i1`;;

let lp_delete_numof_loop =
  new_recursive_definition num_RECURSION
   `(!p:int->bool.
     !i:int.
       lp_delete_numof_loop p i 0 = (&0:int)) /\
    (!p:int->bool.
     !i:int.
     !n:num.
       lp_delete_numof_loop p i (SUC n) =
       (if p i then (&1:int) else (&0:int)) +
       lp_delete_numof_loop p (i + (&1:int)) n)`;;

let lp_delete_numof = new_definition
 `lp_delete_numof
    (keym:A->B) (dummy:A) (xs:A list) (l:int) (u:int) =
    if u <= l then (&0:int)
    else
      lp_delete_numof_loop
        (\i. keym (lp_delete_nth xs i) = keym dummy)
        l (num_of_int (u - l))`;;

let lp_delete_valid = new_definition
 `lp_delete_valid
    (keym:A->B)
    (dummy:A)
    (hash:A->int)
    (entries:A list)
    (present:B->bool)
    (location:B->int) <=>
    ~present (keym dummy) /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH entries):int)
       ==>
       let x = lp_delete_nth entries i in
         ~(keym x = keym dummy)
         ==> present (keym x) /\ location (keym x) = i) /\
    (let n = (&(LENGTH entries):int) in
       !x:A.
         present (keym x)
         ==>
         let i = location (keym x) in
           ((&0:int) <= i /\ i < n) /\
           keym (lp_delete_nth entries i) = keym x /\
           (!j:int.
              (&0:int) <= j /\ j < n
              ==>
              lp_delete_between (lp_delete_bucket hash x n) j i
              ==>
              ~(keym (lp_delete_nth entries j) = keym x) /\
              ~(keym (lp_delete_nth entries j) = keym dummy)))`;;

let lp_delete_relaxed_valid = new_definition
 `lp_delete_relaxed_valid
    (keym:A->B)
    (dummy:A)
    (hash:A->int)
    (entries:A list)
    (present:B->bool)
    (location:B->int)
    (hole:int)
    (scan:int) <=>
    ~present (keym dummy) /\
    (!k:int.
       (&0:int) <= k /\ k < (&(LENGTH entries):int)
       ==>
       let x = lp_delete_nth entries k in
         ~(keym x = keym dummy)
         ==> present (keym x) /\ location (keym x) = k) /\
    (let n = (&(LENGTH entries):int) in
       !x:A.
         present (keym x)
         ==>
         let k = location (keym x) in
           ((&0:int) <= k /\ k < n) /\
           keym (lp_delete_nth entries k) = keym x /\
           (!l:int.
              (&0:int) <= l /\ l < n
              ==>
              lp_delete_between (lp_delete_bucket hash x n) l k
              ==>
              ~(keym (lp_delete_nth entries l) = keym x) /\
              (~(keym (lp_delete_nth entries l) = keym dummy) \/
               l = hole /\ lp_delete_between hole scan k)))`;;

let lp_delete_open_segment = new_definition
 `lp_delete_open_segment
    (keym:A->B)
    (dummy:A)
    (entries:A list)
    (scan:int)
    (finish:int) <=>
    !k:int.
      (&0:int) <= k /\ k < (&(LENGTH entries):int)
      ==>
      lp_delete_between scan k finish
      ==>
      ~(k = scan)
      ==>
      ~(keym (lp_delete_nth entries k) = keym dummy)`;;

let lp_delete_distance = new_definition
 `lp_delete_distance (entries:A list) (finish:int) (i:int) =
    if finish <= i
    then (&(LENGTH entries):int) - i + finish
    else finish - i`;;

let lp_delete_loop_invariant = new_definition
 `lp_delete_loop_invariant
    (keym:A->B)
    (dummy:A)
    (hash:A->int)
    (baseline:int)
    (finish:int)
    (entries:A list)
    (hole:int)
    (scan:int)
    (present:B->bool)
    (location:B->int) <=>
    (&0:int) <= baseline /\
    lp_delete_distance entries finish scan < baseline /\
    ((&0:int) <= finish /\ finish < (&(LENGTH entries):int)) /\
    ((&0:int) <= hole /\ hole < (&(LENGTH entries):int)) /\
    ((&0:int) <= scan /\ scan < (&(LENGTH entries):int)) /\
    ~(hole = finish) /\
    keym (lp_delete_nth entries hole) = keym dummy /\
    keym (lp_delete_nth entries finish) = keym dummy /\
    lp_delete_between hole scan finish /\
    lp_delete_open_segment keym dummy entries scan finish /\
    lp_delete_relaxed_valid
      keym dummy hash entries present location hole scan`;;

ignore
 `!keym:A->B.
  !hash:A->int.
  !dummy:A.
  !f0:int.
  !a:A list.
  !j:int.
  !i:int.
  !view1:B->bool.
  !loc1:B->int.
    ((!k:A. (&0:int) <= hash k) /\
     (!x y:A. keym x = keym y ==> hash x = hash y) /\
     (!n:int.
      !k:A.
        (&0:int) < n
        ==>
        (&0:int) <= lp_delete_bucket hash k n /\
        lp_delete_bucket hash k n < n))
    ==>
    ((&0:int) <= f0 /\ f0 < (&(LENGTH a):int)) /\
    ((&0:int) <= j /\ j < (&(LENGTH a):int)) /\
    ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
    ~(j = f0) /\
    keym (lp_delete_nth a j) = keym dummy /\
    keym (lp_delete_nth a f0) = keym dummy /\
    lp_delete_between j i f0 /\
    lp_delete_open_segment keym dummy a i f0 /\
    lp_delete_relaxed_valid keym dummy hash a view1 loc1 j i
    ==>
    let n = (&(LENGTH a):int) in
    let i1 = lp_delete_next n i in
      ((&0:int) <= i1 /\ i1 < (&(LENGTH a):int)) /\
      (let xi = lp_delete_nth a i1 in
       let o1 = dummy in
         (~(keym xi = keym o1) <=> ~(keym xi = keym o1))
         ==>
         if ~(keym xi = keym o1) then
           (&0:int) < n /\
           (let r = lp_delete_bucket hash xi n in
              (&0:int) <= r /\ r < n
              ==>
              !o2:bool.
                (if j < r
                 then o2 = (r <= i1)
                 else o2 = F)
                ==>
                !o3:bool.
                  (if o2 then
                     o3 = T
                   else
                     ?o4:bool.
                       (if i1 < j
                        then o4 = (j < r)
                        else o4 = F) /\
                       (if o4 then
                          o3 = T
                        else if r <= i1 then
                          o3 = (i1 < j)
                        else
                          o3 = F))
                  ==>
                  if o3 then
                    lp_delete_loop_invariant
                      keym dummy hash
                      (lp_delete_distance a f0 i)
                      f0 a j i1 view1 loc1
                  else
                    !a1:A list.
                      LENGTH a1 = LENGTH a /\
                      (!i2:int.
                         (&0:int) <= i2 /\
                         i2 < (&(LENGTH a1):int)
                         ==>
                         lp_delete_nth a1 i2 = lp_delete_nth a i2)
                      ==>
                      ((&0:int) <= j /\ j < (&(LENGTH a):int)) /\
                      (LENGTH (lp_delete_update_list a j xi) = LENGTH a
                       ==>
                       lp_delete_array_function_equal
                         (lp_delete_update_list a j xi)
                         (lp_delete_nth (lp_delete_update_list a j xi))
                         (lp_delete_update_function
                            (lp_delete_nth a) j xi)
                       ==>
                       !a2:A list.
                         LENGTH a2 =
                           LENGTH (lp_delete_update_list a j xi) /\
                         (!i2:int.
                            (&0:int) <= i2 /\
                            i2 < (&(LENGTH a2):int)
                            ==>
                            lp_delete_nth a2 i2 =
                              lp_delete_nth
                                (lp_delete_update_list a j xi) i2)
                         ==>
                         let o4 = dummy in
                         let moved =
                           lp_delete_update_list a j xi in
                         let cleared =
                           lp_delete_update_list moved i1 o4 in
                           ((&0:int) <= i1 /\
                            i1 < (&(LENGTH moved):int)) /\
                           (LENGTH cleared = LENGTH moved
                            ==>
                            lp_delete_array_function_equal
                              cleared
                              (lp_delete_nth cleared)
                              (lp_delete_update_function
                                 (lp_delete_nth moved) i1 o4)
                            ==>
                            (lp_delete_loop_invariant
                               keym dummy hash
                               (lp_delete_distance a f0 i)
                               f0 cleared i1 i1 view1
                               (lp_delete_update_function
                                  loc1 (keym xi) j) /\
                             (!loc2:B->int.
                              !a3:A list.
                                LENGTH a3 = LENGTH cleared
                                ==>
                                lp_delete_numof
                                  keym dummy a3
                                  (&0:int) (&(LENGTH a3):int) =
                                lp_delete_numof
                                  keym dummy cleared
                                  (&0:int) (&(LENGTH a3):int) /\
                                lp_delete_valid
                                  keym dummy hash a3 view1 loc2
                                ==>
                                lp_delete_numof
                                  keym dummy a3
                                  (&0:int) (&(LENGTH a3):int) =
                                lp_delete_numof
                                  keym dummy a
                                  (&0:int) (&(LENGTH a3):int) /\
                                lp_delete_valid
                                  keym dummy hash a3 view1 loc2)))))
         else
           lp_delete_valid keym dummy hash a view1 loc1)`;;
