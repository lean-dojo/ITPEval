(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2015_dancing_links_DancingLinks_removeqtvc: the dancing
  links removal verification condition for unlinking one node by exact-key
  updates to its neighbors' integer-indexed arrays while preserving the
  circular-list representation. This file contains no proof.
*)

let ntp4vc_dancing_links_sequence_index = new_definition
 `ntp4vc_dancing_links_sequence_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_dancing_links_sequence_nth = new_definition
 `ntp4vc_dancing_links_sequence_nth (xs:int list) (i:int) =
    if ntp4vc_dancing_links_sequence_index i < LENGTH xs
    then EL (ntp4vc_dancing_links_sequence_index i) xs
    else (&0:int)`;;

let ntp4vc_dancing_links_function_update = new_definition
 `ntp4vc_dancing_links_function_update
    (f:int->int) (i:int) (value:int) =
    \j:int. if j = i then value else f j`;;

let ntp4vc_dancing_links_array_length = new_definition
 `ntp4vc_dancing_links_array_length
    (a:int#(int->int)) = FST a`;;

let ntp4vc_dancing_links_array_elts = new_definition
 `ntp4vc_dancing_links_array_elts
    (a:int#(int->int)) = SND a`;;

let ntp4vc_dancing_links_array_update = new_definition
 `ntp4vc_dancing_links_array_update
    (a:int#(int->int)) (i:int) (value:int) =
    (ntp4vc_dancing_links_array_length a,
     ntp4vc_dancing_links_function_update
       (ntp4vc_dancing_links_array_elts a) i value)`;;

let ntp4vc_dancing_links_bounded = new_definition
 `ntp4vc_dancing_links_bounded
    (i:int) (a:int#(int->int)) <=>
    (&0:int) <= i /\
    i < ntp4vc_dancing_links_array_length a`;;

let ntp4vc_dancing_links_context = new_definition
 `ntp4vc_dancing_links_context
    (prev:D->(int#(int->int)))
    (next:D->(int#(int->int)))
    (n:D->int) <=>
    (!self:D.
       (&0:int) <= ntp4vc_dancing_links_array_length (prev self) /\
       (&0:int) <= ntp4vc_dancing_links_array_length (next self) /\
       ntp4vc_dancing_links_array_length (prev self) =
         ntp4vc_dancing_links_array_length (next self) /\
       ntp4vc_dancing_links_array_length (next self) = n self) /\
    (!a b:D.
       prev a = prev b /\ next a = next b /\ n a = n b
       ==> a = b)`;;

let ntp4vc_dancing_links_valid_in = new_definition
 `ntp4vc_dancing_links_valid_in
    (prev:D->(int#(int->int)))
    (next:D->(int#(int->int)))
    (n:D->int) (l:D) (i:int) <=>
    ((&0:int) <= i /\ i < n l) /\
    ((&0:int) <= ntp4vc_dancing_links_array_elts (prev l) i /\
     ntp4vc_dancing_links_array_elts (prev l) i < n l) /\
    ((&0:int) <= ntp4vc_dancing_links_array_elts (next l) i /\
     ntp4vc_dancing_links_array_elts (next l) i < n l) /\
    ntp4vc_dancing_links_array_elts
      (next l) (ntp4vc_dancing_links_array_elts (prev l) i) = i /\
    ntp4vc_dancing_links_array_elts
      (prev l) (ntp4vc_dancing_links_array_elts (next l) i) = i`;;

let ntp4vc_dancing_links_valid_out = new_definition
 `ntp4vc_dancing_links_valid_out
    (prev:D->(int#(int->int)))
    (next:D->(int#(int->int)))
    (n:D->int) (l:D) (i:int) <=>
    ((&0:int) <= i /\ i < n l) /\
    ((&0:int) <= ntp4vc_dancing_links_array_elts (prev l) i /\
     ntp4vc_dancing_links_array_elts (prev l) i < n l) /\
    ((&0:int) <= ntp4vc_dancing_links_array_elts (next l) i /\
     ntp4vc_dancing_links_array_elts (next l) i < n l) /\
    ntp4vc_dancing_links_array_elts
      (next l) (ntp4vc_dancing_links_array_elts (prev l) i) =
      ntp4vc_dancing_links_array_elts (next l) i /\
    ntp4vc_dancing_links_array_elts
      (prev l) (ntp4vc_dancing_links_array_elts (next l) i) =
      ntp4vc_dancing_links_array_elts (prev l) i`;;

let ntp4vc_dancing_links_is_list = new_definition
 `ntp4vc_dancing_links_is_list
    (prev:D->(int#(int->int)))
    (next:D->(int#(int->int)))
    (n:D->int) (l:D) (s:int list) <=>
    !k:int.
      (&0:int) <= k /\ k < (&(LENGTH s):int)
      ==>
      ((&0:int) <= ntp4vc_dancing_links_sequence_nth s k /\
       ntp4vc_dancing_links_sequence_nth s k < n l) /\
      ntp4vc_dancing_links_array_elts
        (prev l) (ntp4vc_dancing_links_sequence_nth s k) =
        ntp4vc_dancing_links_sequence_nth s
          (if k = (&0:int)
           then (&(LENGTH s):int) - (&1:int)
           else k - (&1:int)) /\
      ntp4vc_dancing_links_array_elts
        (next l) (ntp4vc_dancing_links_sequence_nth s k) =
        ntp4vc_dancing_links_sequence_nth s
          (if k = (&(LENGTH s):int) - (&1:int)
           then (&0:int)
           else k + (&1:int)) /\
      (!k':int.
         (&0:int) <= k' /\ k' < (&(LENGTH s):int)
         ==>
         ~(k = k')
         ==>
         ~(ntp4vc_dancing_links_sequence_nth s k =
           ntp4vc_dancing_links_sequence_nth s k'))`;;

let ntp4vc_dancing_links_all_result_records = new_definition
 `ntp4vc_dancing_links_all_result_records
    (prev:D->(int#(int->int)))
    (next:D->(int#(int->int)))
    (n:D->int) (l:D) (i:int) (s:int list)
    (updated_prev:int#(int->int))
    (previous_index:int) (next_index:int) <=>
    let updated_next =
      ntp4vc_dancing_links_array_update
        (next l) previous_index next_index in
    !l1:D.
      ntp4vc_dancing_links_array_length updated_next =
        ntp4vc_dancing_links_array_length (next l)
      ==>
      ntp4vc_dancing_links_array_length updated_next =
        ntp4vc_dancing_links_array_length (next l)
      ==>
      ntp4vc_dancing_links_array_elts updated_next =
        ntp4vc_dancing_links_function_update
          (ntp4vc_dancing_links_array_elts (next l))
          previous_index next_index
      ==>
      (ntp4vc_dancing_links_array_length updated_prev =
         ntp4vc_dancing_links_array_length updated_next /\
       ntp4vc_dancing_links_array_length updated_next = n l) /\
      (n l = n l1 /\
       updated_next = next l1 /\
       updated_prev = prev l1
       ==>
       ntp4vc_dancing_links_valid_out prev next n l1 i /\
       ntp4vc_dancing_links_is_list prev next n l1 s)`;;

let ntp4vc_dancing_links_remove_conclusion = new_definition
 `ntp4vc_dancing_links_remove_conclusion
    (prev:D->(int#(int->int)))
    (next:D->(int#(int->int)))
    (n:D->int) (l:D) (i:int) (s:int list) <=>
    let o1 = prev l in
    ntp4vc_dancing_links_bounded i o1 /\
    (let o2 = ntp4vc_dancing_links_array_elts o1 i in
     let o3 = next l in
     ntp4vc_dancing_links_bounded i o3 /\
     (let o4 = ntp4vc_dancing_links_array_elts o3 i in
      let o5 = prev l in
      ntp4vc_dancing_links_bounded o4 o5 /\
      (let updated_prev =
         ntp4vc_dancing_links_array_update o5 o4 o2 in
       ntp4vc_dancing_links_array_length updated_prev =
         ntp4vc_dancing_links_array_length o5
       ==>
       ntp4vc_dancing_links_array_length updated_prev =
         ntp4vc_dancing_links_array_length (prev l)
       ==>
       ntp4vc_dancing_links_array_elts updated_prev =
         ntp4vc_dancing_links_function_update
           (ntp4vc_dancing_links_array_elts o5) o4 o2
       ==>
       ntp4vc_dancing_links_bounded i (next l) /\
       (let o6 = ntp4vc_dancing_links_array_elts (next l) i in
        ntp4vc_dancing_links_bounded i updated_prev /\
        (let o7 = ntp4vc_dancing_links_array_elts updated_prev i in
         ntp4vc_dancing_links_bounded o7 (next l) /\
         ntp4vc_dancing_links_all_result_records
           prev next n l i s updated_prev o7 o6)))))`;;

let statement =
 `!prev:D->(int#(int->int)).
  !next:D->(int#(int->int)).
  !n:D->int.
    ntp4vc_dancing_links_context prev next n
    ==>
    !l:D.
    !i:int.
    !s:int list.
      ntp4vc_dancing_links_valid_in prev next n l i
      ==>
      ntp4vc_dancing_links_is_list prev next n l (CONS i s)
      ==>
      ntp4vc_dancing_links_remove_conclusion prev next n l i s`;;
