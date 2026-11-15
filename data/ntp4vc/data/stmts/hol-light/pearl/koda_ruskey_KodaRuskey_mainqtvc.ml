(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/koda_ruskey_KodaRuskey_mainqtvc: the Koda-Ruskey forest-coloring
  main verification condition, asserting the initial stack invariants and
  complete enumeration of distinct valid colorings. This file contains no proof.
*)

let ntp4vc_kr_color_INDUCT,ntp4vc_kr_color_RECURSION = define_type
  "ntp4vc_kr_color =
       NTP4VC_KR_White
     | NTP4VC_KR_Black";;

let ntp4vc_kr_forest_INDUCT,ntp4vc_kr_forest_RECURSION = define_type
  "ntp4vc_kr_forest =
       NTP4VC_KR_E
     | NTP4VC_KR_N int ntp4vc_kr_forest ntp4vc_kr_forest";;

let ntp4vc_kr_int_index = new_definition
 `ntp4vc_kr_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_kr_nth = new_definition
 `ntp4vc_kr_nth (xs:A list) (i:int) =
    if ntp4vc_kr_int_index i < LENGTH xs
    then EL (ntp4vc_kr_int_index i) xs
    else ARB`;;

let ntp4vc_kr_bits = new_definition
 `ntp4vc_kr_bits (bits:ntp4vc_kr_color list) =
    \i:int. ntp4vc_kr_nth bits i`;;

let ntp4vc_kr_size_forest =
  new_recursive_definition ntp4vc_kr_forest_RECURSION
   `(ntp4vc_kr_size_forest NTP4VC_KR_E = (&0:int)) /\
    (!i:int.
     !f1 f2:ntp4vc_kr_forest.
       ntp4vc_kr_size_forest (NTP4VC_KR_N i f1 f2) =
       (&1:int) +
       ntp4vc_kr_size_forest f1 +
       ntp4vc_kr_size_forest f2)`;;

let ntp4vc_kr_mem_forest =
  new_recursive_definition ntp4vc_kr_forest_RECURSION
   `(!n:int.
       ntp4vc_kr_mem_forest n NTP4VC_KR_E = F) /\
    (!n i:int.
     !f1 f2:ntp4vc_kr_forest.
       ntp4vc_kr_mem_forest n (NTP4VC_KR_N i f1 f2) =
       (i = n \/
        ntp4vc_kr_mem_forest n f1 \/
        ntp4vc_kr_mem_forest n f2))`;;

let ntp4vc_kr_between_range_forest = new_definition
 `ntp4vc_kr_between_range_forest
    (lo:int) (hi:int) (f:ntp4vc_kr_forest) <=>
    !n:int.
      ntp4vc_kr_mem_forest n f ==> lo <= n /\ n < hi`;;

let ntp4vc_kr_disjoint = new_definition
 `ntp4vc_kr_disjoint
    (f1:ntp4vc_kr_forest) (f2:ntp4vc_kr_forest) <=>
    !x:int.
      ntp4vc_kr_mem_forest x f1
      ==> ~ntp4vc_kr_mem_forest x f2`;;

let ntp4vc_kr_no_repeated_forest =
  new_recursive_definition ntp4vc_kr_forest_RECURSION
   `(ntp4vc_kr_no_repeated_forest NTP4VC_KR_E = T) /\
    (!i:int.
     !f1 f2:ntp4vc_kr_forest.
       ntp4vc_kr_no_repeated_forest (NTP4VC_KR_N i f1 f2) =
       (ntp4vc_kr_no_repeated_forest f1 /\
        ntp4vc_kr_no_repeated_forest f2 /\
        ~ntp4vc_kr_mem_forest i f1 /\
        ~ntp4vc_kr_mem_forest i f2 /\
        ntp4vc_kr_disjoint f1 f2))`;;

let ntp4vc_kr_valid_nums_forest = new_definition
 `ntp4vc_kr_valid_nums_forest (f:ntp4vc_kr_forest) (n:int) <=>
    ntp4vc_kr_between_range_forest (&0:int) n f /\
    ntp4vc_kr_no_repeated_forest f`;;

let ntp4vc_kr_white_forest =
  new_recursive_definition ntp4vc_kr_forest_RECURSION
   `(!c:int->ntp4vc_kr_color.
       ntp4vc_kr_white_forest NTP4VC_KR_E c = T) /\
    (!i:int.
     !f1 f2:ntp4vc_kr_forest.
     !c:int->ntp4vc_kr_color.
       ntp4vc_kr_white_forest (NTP4VC_KR_N i f1 f2) c =
       (c i = NTP4VC_KR_White /\
        ntp4vc_kr_white_forest f1 c /\
        ntp4vc_kr_white_forest f2 c))`;;

let ntp4vc_kr_valid_coloring =
  new_recursive_definition ntp4vc_kr_forest_RECURSION
   `(!c:int->ntp4vc_kr_color.
       ntp4vc_kr_valid_coloring NTP4VC_KR_E c = T) /\
    (!i:int.
     !f1 f2:ntp4vc_kr_forest.
     !c:int->ntp4vc_kr_color.
       ntp4vc_kr_valid_coloring (NTP4VC_KR_N i f1 f2) c =
       (ntp4vc_kr_valid_coloring f2 c /\
        (if c i = NTP4VC_KR_White
         then ntp4vc_kr_white_forest f1 c
         else ntp4vc_kr_valid_coloring f1 c)))`;;

let ntp4vc_kr_count_forest =
  new_recursive_definition ntp4vc_kr_forest_RECURSION
   `(ntp4vc_kr_count_forest NTP4VC_KR_E = (&1:int)) /\
    (!i:int.
     !f1 f2:ntp4vc_kr_forest.
       ntp4vc_kr_count_forest (NTP4VC_KR_N i f1 f2) =
       ((&1:int) + ntp4vc_kr_count_forest f1) *
       ntp4vc_kr_count_forest f2)`;;

let ntp4vc_kr_eq_coloring = new_definition
 `ntp4vc_kr_eq_coloring
    (n:int)
    (c1:int->ntp4vc_kr_color)
    (c2:int->ntp4vc_kr_color) <=>
    !i:int. (&0:int) <= i /\ i < n ==> c1 i = c2 i`;;

let ntp4vc_kr_mem_stack =
  new_recursive_definition list_RECURSION
   `(!n:int.
       ntp4vc_kr_mem_stack n ([]:ntp4vc_kr_forest list) = F) /\
    (!n:int.
     !f:ntp4vc_kr_forest.
     !st:ntp4vc_kr_forest list.
       ntp4vc_kr_mem_stack n (CONS f st) =
       (ntp4vc_kr_mem_forest n f \/ ntp4vc_kr_mem_stack n st))`;;

let ntp4vc_kr_even_forest =
  new_recursive_definition ntp4vc_kr_forest_RECURSION
   `(ntp4vc_kr_even_forest NTP4VC_KR_E = F) /\
    (!i:int.
     !f1 f2:ntp4vc_kr_forest.
       ntp4vc_kr_even_forest (NTP4VC_KR_N i f1 f2) =
       (~ntp4vc_kr_even_forest f1 \/ ntp4vc_kr_even_forest f2))`;;

let ntp4vc_kr_final_forest =
  new_recursive_definition ntp4vc_kr_forest_RECURSION
   `(!c:int->ntp4vc_kr_color.
       ntp4vc_kr_final_forest NTP4VC_KR_E c = T) /\
    (!i:int.
     !f1 f2:ntp4vc_kr_forest.
     !c:int->ntp4vc_kr_color.
       ntp4vc_kr_final_forest (NTP4VC_KR_N i f1 f2) c =
       (c i = NTP4VC_KR_Black /\
        ntp4vc_kr_final_forest f1 c /\
        (if ~ntp4vc_kr_even_forest f1
         then ntp4vc_kr_white_forest f2 c
         else ntp4vc_kr_final_forest f2 c)))`;;

let ntp4vc_kr_unchanged = new_definition
 `ntp4vc_kr_unchanged
    (st:ntp4vc_kr_forest list)
    (c1:int->ntp4vc_kr_color)
    (c2:int->ntp4vc_kr_color) <=>
    !i:int. ntp4vc_kr_mem_stack i st ==> c1 i = c2 i`;;

let ntp4vc_kr_inverse =
  new_recursive_definition list_RECURSION
   `(!c1 c2:int->ntp4vc_kr_color.
       ntp4vc_kr_inverse ([]:ntp4vc_kr_forest list) c1 c2 = T) /\
    (!f:ntp4vc_kr_forest.
     !st:ntp4vc_kr_forest list.
     !c1 c2:int->ntp4vc_kr_color.
       ntp4vc_kr_inverse (CONS f st) c1 c2 =
       ((ntp4vc_kr_white_forest f c1 /\
         ntp4vc_kr_final_forest f c2 \/
         ntp4vc_kr_final_forest f c1 /\
         ntp4vc_kr_white_forest f c2) /\
        (if ntp4vc_kr_even_forest f
         then ntp4vc_kr_unchanged st c1 c2
         else ntp4vc_kr_inverse st c1 c2)))`;;

let ntp4vc_kr_any_stack =
  new_recursive_definition list_RECURSION
   `(!c:int->ntp4vc_kr_color.
       ntp4vc_kr_any_stack ([]:ntp4vc_kr_forest list) c = T) /\
    (!f:ntp4vc_kr_forest.
     !st:ntp4vc_kr_forest list.
     !c:int->ntp4vc_kr_color.
       ntp4vc_kr_any_stack (CONS f st) c =
       ((ntp4vc_kr_white_forest f c \/
         ntp4vc_kr_final_forest f c) /\
        ntp4vc_kr_any_stack st c))`;;

let ntp4vc_kr_sub_RULES,
    ntp4vc_kr_sub_INDUCT,
    ntp4vc_kr_sub_CASES =
  new_inductive_definition
   `(!f:ntp4vc_kr_forest.
     !c:int->ntp4vc_kr_color.
       ntp4vc_kr_sub [f] f c) /\
    (!st:ntp4vc_kr_forest list.
     !f2:ntp4vc_kr_forest.
     !c:int->ntp4vc_kr_color.
     !i:int.
     !f1:ntp4vc_kr_forest.
       ntp4vc_kr_sub st f2 c
       ==> ntp4vc_kr_sub st (NTP4VC_KR_N i f1 f2) c) /\
    (!st:ntp4vc_kr_forest list.
     !f1:ntp4vc_kr_forest.
     !c:int->ntp4vc_kr_color.
     !i:int.
     !f2:ntp4vc_kr_forest.
       ntp4vc_kr_sub st f1 c /\
       c i = NTP4VC_KR_Black
       ==> ntp4vc_kr_sub
             (APPEND st [f2]) (NTP4VC_KR_N i f1 f2) c)`;;

let ntp4vc_kr_count_stack =
  new_recursive_definition list_RECURSION
   `(ntp4vc_kr_count_stack ([]:ntp4vc_kr_forest list) = (&1:int)) /\
    (!f:ntp4vc_kr_forest.
     !st:ntp4vc_kr_forest list.
       ntp4vc_kr_count_stack (CONS f st) =
       ntp4vc_kr_count_forest f * ntp4vc_kr_count_stack st)`;;

let ntp4vc_kr_stored_solutions = new_definition
 `ntp4vc_kr_stored_solutions
    (f0:ntp4vc_kr_forest)
    (bits:int->ntp4vc_kr_color)
    (st:ntp4vc_kr_forest list)
    (v1:(int->ntp4vc_kr_color) list)
    (v2:(int->ntp4vc_kr_color) list) <=>
    let n = ntp4vc_kr_size_forest f0 in
    let start = (&(LENGTH v1):int) in
    let stop = (&(LENGTH v2):int) in
    stop - start = ntp4vc_kr_count_stack st /\
    (!j:int.
       (&0:int) <= j /\ j < start
       ==> ntp4vc_kr_eq_coloring n
             (ntp4vc_kr_nth v2 j) (ntp4vc_kr_nth v1 j)) /\
    (!j:int.
       start <= j /\ j < stop
       ==> ntp4vc_kr_valid_coloring f0 (ntp4vc_kr_nth v2 j) /\
           (!i:int.
              (&0:int) <= i /\ i < n
              ==> ~ntp4vc_kr_mem_stack i st
              ==> (ntp4vc_kr_nth v2 j) i = bits i) /\
           (!k:int.
              start <= k /\ k < stop
              ==> ~(j = k)
              ==> ~ntp4vc_kr_eq_coloring n
                    (ntp4vc_kr_nth v2 j)
                    (ntp4vc_kr_nth v2 k)))`;;

let statement =
 `!f0:ntp4vc_kr_forest.
  !bits:ntp4vc_kr_color list.
    ntp4vc_kr_white_forest f0 (ntp4vc_kr_bits bits)
    ==>
    ntp4vc_kr_size_forest f0 = (&(LENGTH bits):int)
    ==>
    ntp4vc_kr_valid_nums_forest f0 (&(LENGTH bits):int)
    ==>
    let o1 = [f0] in
    (ntp4vc_kr_size_forest f0 = (&(LENGTH bits):int) /\
     ntp4vc_kr_valid_nums_forest f0 (&(LENGTH bits):int) /\
     ntp4vc_kr_sub o1 f0 (ntp4vc_kr_bits bits) /\
     ntp4vc_kr_any_stack o1 (ntp4vc_kr_bits bits) /\
     ntp4vc_kr_valid_coloring f0 (ntp4vc_kr_bits bits)) /\
    (!bits1:ntp4vc_kr_color list.
     !visited:(int->ntp4vc_kr_color) list.
       LENGTH bits1 = LENGTH bits
       ==>
       ((!i:int.
           ~ntp4vc_kr_mem_stack i o1
           ==> ntp4vc_kr_nth bits1 i = ntp4vc_kr_nth bits i) /\
        ntp4vc_kr_inverse
          o1 (ntp4vc_kr_bits bits) (ntp4vc_kr_bits bits1) /\
        ntp4vc_kr_valid_coloring f0 (ntp4vc_kr_bits bits1) /\
        ntp4vc_kr_stored_solutions
          f0 (ntp4vc_kr_bits bits1) o1 [] visited)
       ==>
       (&(LENGTH visited):int) = ntp4vc_kr_count_forest f0 /\
       (let n = (&(LENGTH visited):int) in
        !j:int.
          (&0:int) <= j /\ j < n
          ==>
          ntp4vc_kr_valid_coloring f0 (ntp4vc_kr_nth visited j) /\
          (!k:int.
             (&0:int) <= k /\ k < n
             ==> ~(j = k)
             ==> ~ntp4vc_kr_eq_coloring
                   (&(LENGTH bits1):int)
                   (ntp4vc_kr_nth visited j)
                   (ntp4vc_kr_nth visited k))))`;;
