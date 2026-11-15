(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_lexicographic_permutations_1_Top_to_seqqtvc: the
  verification condition for copying an integer array into a finite sequence,
  including loop initialization, preservation, exit, and indexed-value
  obligations. This file contains no proof.
*)

let ntp4vc_lexperm_to_seq_index = new_definition
 `ntp4vc_lexperm_to_seq_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_lexperm_to_seq_nth = new_definition
 `ntp4vc_lexperm_to_seq_nth (s:int list) (i:int) =
    if ntp4vc_lexperm_to_seq_index i < LENGTH s
    then EL (ntp4vc_lexperm_to_seq_index i) s
    else (&0:int)`;;

let ntp4vc_lexperm_to_seq_copy = new_definition
 `ntp4vc_lexperm_to_seq_copy (s:int list) (a:int list) <=>
    LENGTH s = LENGTH a /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH s):int)
       ==>
       ntp4vc_lexperm_to_seq_nth s i =
       ntp4vc_lexperm_to_seq_nth a i)`;;

let ntp4vc_lexperm_to_seq_initial = new_definition
 `ntp4vc_lexperm_to_seq_initial (a:int list) <=>
    (&(LENGTH ([]:int list)):int) = (&0:int) /\
    (!i:int.
       (&0:int) <= i /\ i < (&0:int)
       ==>
       ntp4vc_lexperm_to_seq_nth ([]:int list) i =
       ntp4vc_lexperm_to_seq_nth a i)`;;

let ntp4vc_lexperm_to_seq_snoc_facts = new_definition
 `ntp4vc_lexperm_to_seq_snoc_facts
    (s:int list) (o2:int) (o3:int list) <=>
    (&(LENGTH o3):int) = (&1:int) + (&(LENGTH s):int) /\
    ntp4vc_lexperm_to_seq_nth o3 (&(LENGTH s):int) = o2 /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH s):int)
       ==>
       ntp4vc_lexperm_to_seq_nth o3 i =
       ntp4vc_lexperm_to_seq_nth s i)`;;

let ntp4vc_lexperm_to_seq_step_post = new_definition
 `ntp4vc_lexperm_to_seq_step_post
    (a:int list) (s:int list) (o3:int list) <=>
    (&(LENGTH o3):int) = (&(LENGTH s):int) + (&1:int) /\
    (!i:int.
       (&0:int) <= i /\
       i < (&(LENGTH s):int) + (&1:int)
       ==>
       ntp4vc_lexperm_to_seq_nth o3 i =
       ntp4vc_lexperm_to_seq_nth a i)`;;

let ntp4vc_lexperm_to_seq_append_obligation = new_definition
 `ntp4vc_lexperm_to_seq_append_obligation
    (a:int list) (s:int list) <=>
    ntp4vc_lexperm_to_seq_snoc_facts
      s
      (ntp4vc_lexperm_to_seq_nth a (&(LENGTH s):int))
      (APPEND s [ntp4vc_lexperm_to_seq_nth a (&(LENGTH s):int)])
    ==>
    ntp4vc_lexperm_to_seq_step_post
      a s
      (APPEND s [ntp4vc_lexperm_to_seq_nth a (&(LENGTH s):int)])`;;

let ntp4vc_lexperm_to_seq_step = new_definition
 `ntp4vc_lexperm_to_seq_step
    (a:int list) (o1:int) (s:int list) <=>
    (((&0:int) <= (&(LENGTH s):int) /\
      (&(LENGTH s):int) <= o1) /\
     (!i:int.
        (&0:int) <= i /\ i < (&(LENGTH s):int)
        ==>
        ntp4vc_lexperm_to_seq_nth s i =
        ntp4vc_lexperm_to_seq_nth a i))
    ==>
    ((&0:int) <= (&(LENGTH s):int) /\ LENGTH s < LENGTH a) /\
    ntp4vc_lexperm_to_seq_append_obligation a s`;;

let ntp4vc_lexperm_to_seq_exit = new_definition
 `ntp4vc_lexperm_to_seq_exit
    (a:int list) (o1:int) (s:int list) <=>
    ((&(LENGTH s):int) = o1 + (&1:int) /\
     (!i:int.
        (&0:int) <= i /\ i < o1 + (&1:int)
        ==>
        ntp4vc_lexperm_to_seq_nth s i =
        ntp4vc_lexperm_to_seq_nth a i))
    ==>
    ntp4vc_lexperm_to_seq_copy s a`;;

let statement =
 `!a:int list.
    let o1 = (&(LENGTH a):int) - (&1:int) in
    (((&0:int) <= o1 + (&1:int)
      ==>
      ntp4vc_lexperm_to_seq_initial a /\
      (!s:int list.
         ntp4vc_lexperm_to_seq_step a o1 s /\
         ntp4vc_lexperm_to_seq_exit a o1 s)) /\
     (o1 + (&1:int) < (&0:int)
      ==>
      let r = ([]:int list) in
      ntp4vc_lexperm_to_seq_copy r a))`;;
