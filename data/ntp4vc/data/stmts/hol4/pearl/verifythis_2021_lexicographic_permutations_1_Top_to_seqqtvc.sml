(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_lexicographic_permutations_1_Top_to_seqqtvc: the
  verification condition for copying an integer array into a finite sequence
  while preserving its length and every indexed value through loop
  initialization, append preservation, and loop exit. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val ntp4vc_lexperm_to_seq_index_def = Define `
  ntp4vc_lexperm_to_seq_index (i : int) =
    if i < (0 : int) then 0 else Num i`;

val ntp4vc_lexperm_to_seq_nth_def = Define `
  ntp4vc_lexperm_to_seq_nth (s : int list) (i : int) =
    if ntp4vc_lexperm_to_seq_index i < LENGTH s
    then EL (ntp4vc_lexperm_to_seq_index i) s
    else (0 : int)`;

val ntp4vc_lexperm_to_seq_prefix_copy_def = Define `
  ntp4vc_lexperm_to_seq_prefix_copy
    (s : int list) (a : int list) (bound : int) <=>
    !i : int.
      (0 : int) <= i /\ i < bound
      ==> ntp4vc_lexperm_to_seq_nth s i =
          ntp4vc_lexperm_to_seq_nth a i`;

val ntp4vc_lexperm_to_seq_snoc_spec_def = Define `
  ntp4vc_lexperm_to_seq_snoc_spec
    (old : int list) (added : int) (new : int list) <=>
    &(LENGTH new) = (1 : int) + &(LENGTH old) /\
    ntp4vc_lexperm_to_seq_nth new (&(LENGTH old)) = added /\
    (!i : int.
       (0 : int) <= i /\ i < &(LENGTH old)
       ==> ntp4vc_lexperm_to_seq_nth new i =
           ntp4vc_lexperm_to_seq_nth old i)`;

val verifythis_2021_lexicographic_permutations_1_Top_to_seqqtvc_statement =
  ``!a : int list.
      let o1 = &(LENGTH a) - (1 : int) in
      (((0 : int) <= o1 + (1 : int)
        ==>
        ((&(LENGTH ([] : int list)) : int) = (0 : int) /\
         ntp4vc_lexperm_to_seq_prefix_copy
           ([] : int list) a (0 : int)) /\
        (!s : int list.
           (((((0 : int) <= &(LENGTH s) /\
               &(LENGTH s) <= o1) /\
              ntp4vc_lexperm_to_seq_prefix_copy
                s a (&(LENGTH s)))
             ==>
             (((0 : int) <= &(LENGTH s) /\
               &(LENGTH s) < &(LENGTH a)) /\
              (let o2 =
                 ntp4vc_lexperm_to_seq_nth a (&(LENGTH s))
               in
               let o3 = APPEND s [o2] in
                 ntp4vc_lexperm_to_seq_snoc_spec s o2 o3
                 ==>
                 &(LENGTH o3) = &(LENGTH s) + (1 : int) /\
                 ntp4vc_lexperm_to_seq_prefix_copy
                   o3 a (&(LENGTH s) + (1 : int))))) /\
            ((&(LENGTH s) = o1 + (1 : int) /\
              ntp4vc_lexperm_to_seq_prefix_copy
                s a (o1 + (1 : int)))
             ==>
             LENGTH s = LENGTH a /\
             ntp4vc_lexperm_to_seq_prefix_copy
               s a (&(LENGTH s))))))
       /\
       (o1 + (1 : int) < (0 : int)
        ==>
        let r = ([] : int list) in
          LENGTH r = LENGTH a /\
          ntp4vc_lexperm_to_seq_prefix_copy
            r a (&(LENGTH r))))``;
