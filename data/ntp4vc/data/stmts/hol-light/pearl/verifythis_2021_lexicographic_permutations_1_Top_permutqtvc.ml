(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_lexicographic_permutations_1_Top_permutqtvc: the
  verification condition for enumerating every integer permutation exactly
  through a strictly increasing lexicographic traversal, including the loop
  invariant and finite-set termination variant. This file contains no proof.
*)

let ntp4vc_permut_index = new_definition
 `ntp4vc_permut_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_permut_nth = new_definition
 `ntp4vc_permut_nth (s:int list) (i:int) =
    if ntp4vc_permut_index i < LENGTH s
    then EL (ntp4vc_permut_index i) s
    else (&0:int)`;;

let ntp4vc_permut_occ_all = new_definition
 `ntp4vc_permut_occ_all (x:int) (s:int list) =
    (&(LENGTH (FILTER (\y:int. y = x) s)):int)`;;

let ntp4vc_permut_is_permutation = new_definition
 `ntp4vc_permut_is_permutation (p:int list) (a:int list) <=>
    LENGTH p = LENGTH a /\
    (!x:int.
       ntp4vc_permut_occ_all x p =
       ntp4vc_permut_occ_all x a)`;;

let ntp4vc_permut_lt = new_definition
 `ntp4vc_permut_lt (p:int list) (q:int list) <=>
    (LENGTH p = LENGTH q /\ (&0:int) < (&(LENGTH q):int)) /\
    (?i:int.
       ((&0:int) <= i /\ i < (&(LENGTH p):int)) /\
       (!j:int.
          (&0:int) <= j /\ j < i
          ==> ntp4vc_permut_nth p j = ntp4vc_permut_nth q j) /\
       ntp4vc_permut_nth p i < ntp4vc_permut_nth q i)`;;

let ntp4vc_permut_to_seq = new_definition
 `ntp4vc_permut_to_seq (a:int list) = a`;;

let ntp4vc_permut_all = new_definition
 `ntp4vc_permut_all (s:int list) =
    {p:int list |
       LENGTH p = LENGTH s /\
       (!i:num. i < LENGTH p ==> MEM (EL i p) s)}`;;

let ntp4vc_permut_seq_copy = new_definition
 `ntp4vc_permut_seq_copy (s:int list) (a:int list) <=>
    LENGTH s = LENGTH a /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH s):int)
       ==> ntp4vc_permut_nth s i = ntp4vc_permut_nth a i)`;;

let ntp4vc_permut_ascending = new_definition
 `ntp4vc_permut_ascending (a:int list) <=>
    !i j:int.
      (&0:int) <= i /\ i <= j /\ j < (&(LENGTH a):int)
      ==> ntp4vc_permut_nth a i <= ntp4vc_permut_nth a j`;;

let ntp4vc_permut_snoc_spec = new_definition
 `ntp4vc_permut_snoc_spec
    (base:(int list) list) (result:(int list) list) (x:int list) <=>
    (&(LENGTH result):int) =
      (&1:int) + (&(LENGTH base):int) /\
    EL (LENGTH base) result = x /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH base):int)
       ==> EL (ntp4vc_permut_index i) result =
           EL (ntp4vc_permut_index i) base)`;;

let ntp4vc_permut_loop_invariant = new_definition
 `ntp4vc_permut_loop_invariant
    (all1:(int list)->bool)
    (a0:int list)
    (seen:(int list)->bool)
    (result:(int list) list)
    (current:int list) <=>
    (&0:int) < (&(LENGTH result):int) /\
    ntp4vc_permut_is_permutation current a0 /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH result):int)
       ==> ntp4vc_permut_is_permutation
             (EL (ntp4vc_permut_index i) result) a0) /\
    EL (ntp4vc_permut_index
          ((&(LENGTH result):int) - (&1:int))) result =
      current /\
    ntp4vc_permut_is_permutation
      (EL (ntp4vc_permut_index
            ((&(LENGTH result):int) - (&1:int))) result) a0 /\
    (!i j:int.
       (&0:int) <= i /\ i < j /\ j < (&(LENGTH result):int)
       ==> ntp4vc_permut_lt
             (EL (ntp4vc_permut_index i) result)
             (EL (ntp4vc_permut_index j) result)) /\
    (!p:int list.
       ntp4vc_permut_is_permutation p a0
       ==> ntp4vc_permut_lt p current
       ==> ?i:int.
             ((&0:int) <= i /\
              i < (&(LENGTH result):int) - (&1:int)) /\
             EL (ntp4vc_permut_index i) result = p) /\
    (!p:int list.
       p IN seen <=>
       ?i:int.
         ((&0:int) <= i /\ i < (&(LENGTH result):int)) /\
         EL (ntp4vc_permut_index i) result = p) /\
    seen SUBSET all1`;;

let ntp4vc_permut_complete = new_definition
 `ntp4vc_permut_complete (a:int list) (result:(int list) list) <=>
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH result):int)
       ==> ntp4vc_permut_is_permutation
             (EL (ntp4vc_permut_index i) result) a) /\
    (!i j:int.
       (&0:int) <= i /\ i < j /\ j < (&(LENGTH result):int)
       ==> ntp4vc_permut_lt
             (EL (ntp4vc_permut_index i) result)
             (EL (ntp4vc_permut_index j) result)) /\
    (!p:int list.
       ntp4vc_permut_is_permutation p a
       ==> ?i:int.
             ((&0:int) <= i /\ i < (&(LENGTH result):int)) /\
             EL (ntp4vc_permut_index i) result = p)`;;

let statement =
 `!all_permutations:int list->(int list->bool).
    (!s:int list. FINITE (all_permutations s)) /\
    (!p s:int list.
       ntp4vc_permut_is_permutation p s
       ==> p IN all_permutations s)
    ==>
  !a:int list.
    let a0 = ntp4vc_permut_to_seq a in
    ntp4vc_permut_seq_copy a0 a
    ==>
    let all1 = all_permutations a0 in
    (!p:int list.
       ntp4vc_permut_is_permutation p a0 ==> p IN all1)
    ==>
    !a1:int list.
      LENGTH a1 = LENGTH a
      ==>
      ntp4vc_permut_ascending a1 /\
      ntp4vc_permut_is_permutation
        (ntp4vc_permut_to_seq a1) (ntp4vc_permut_to_seq a)
      ==>
      let o1 = ntp4vc_permut_to_seq a1 in
      ntp4vc_permut_seq_copy o1 a1
      ==>
      let o2 = ([]:(int list) list) in
      let o3 = APPEND o2 [o1] in
      ntp4vc_permut_snoc_spec o2 o3 o1
      ==>
      let o4 = ntp4vc_permut_to_seq a1 in
      ntp4vc_permut_seq_copy o4 a1
      ==>
      let o5 = ntp4vc_permut_to_seq a1 in
      ntp4vc_permut_seq_copy o5 a1
      ==>
      let o6 = o5 INSERT ({}:(int list)->bool) in
      (ntp4vc_permut_is_permutation
         (ntp4vc_permut_to_seq a1) a0 /\
       o4 = ntp4vc_permut_to_seq a1 /\
       ntp4vc_permut_loop_invariant all1 a0 o6 o3 o4) /\
      (!seen:(int list)->bool.
       !result:(int list) list.
       !a2:int list.
         LENGTH a2 = LENGTH a1
         ==>
         ntp4vc_permut_loop_invariant
           all1 a0 seen result (ntp4vc_permut_to_seq a2)
         ==>
         (LENGTH a2 = LENGTH a0 /\
          ntp4vc_permut_is_permutation
            (ntp4vc_permut_to_seq a2) a0) /\
         (!a3:int list.
            LENGTH a3 = LENGTH a2
            ==>
            !o7:bool.
              ntp4vc_permut_is_permutation
                (ntp4vc_permut_to_seq a3) a0 /\
              (o7 = F ==> ntp4vc_permut_seq_copy a3 a2) /\
              (o7 = F
               ==> !p:int list.
                     ntp4vc_permut_is_permutation p a0
                     ==> ~ntp4vc_permut_lt
                           (ntp4vc_permut_to_seq a3) p) /\
              (o7 = T
               ==> ntp4vc_permut_lt
                     (ntp4vc_permut_to_seq a2)
                     (ntp4vc_permut_to_seq a3)) /\
              (o7 = T
               ==> !p:int list.
                     ntp4vc_permut_is_permutation p a0
                     ==> ~(ntp4vc_permut_lt
                             (ntp4vc_permut_to_seq a2) p /\
                           ntp4vc_permut_lt
                             p (ntp4vc_permut_to_seq a3)))
              ==>
              if o7 = T then
                let o8 = ntp4vc_permut_to_seq a3 in
                ntp4vc_permut_seq_copy o8 a3
                ==>
                let o9 = APPEND result [o8] in
                ntp4vc_permut_snoc_spec result o9 o8
                ==>
                let o10 = ntp4vc_permut_to_seq a3 in
                ntp4vc_permut_seq_copy o10 a3
                ==>
                let o11 = ntp4vc_permut_to_seq a3 in
                ntp4vc_permut_seq_copy o11 a3
                ==>
                ((&0:int) <=
                   (&(CARD all1):int) - (&(CARD seen):int) /\
                 (&(CARD all1):int) -
                     (&(CARD (o11 INSERT seen)):int) <
                   (&(CARD all1):int) - (&(CARD seen):int)) /\
                ntp4vc_permut_is_permutation
                  (ntp4vc_permut_to_seq a3) a0 /\
                o10 = ntp4vc_permut_to_seq a3 /\
                ntp4vc_permut_loop_invariant
                  all1 a0 (o11 INSERT seen) o9 o10
              else
                ntp4vc_permut_complete
                  (ntp4vc_permut_to_seq a) result))`;;
