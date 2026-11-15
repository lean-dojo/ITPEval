(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1057919,
  "Sylow theorems": existence of subgroups of prescribed prime-power order,
  conjugacy of Sylow p-subgroups, divisibility of their count by subgroup
  index, and congruence of that count to one modulo p. This file contains no
  proof.
*)

let sylow_output = open_out "/dev/null";;
let sylow_formatter = Format.formatter_of_out_channel sylow_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file sylow_formatter path);;
let sylow_library_loaded =
  Toploop.use_file sylow_formatter "Library/grouptheory.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush sylow_formatter ();;
close_out sylow_output;;
if not sylow_library_loaded then
  failwith "failed to load Library/grouptheory.ml";;

let SYLOW_EXISTS_SUBGROUP_CARD_POW_PRIME =
  `!G:A group. !p n:num.
     FINITE (group_carrier G) /\
     prime p /\
     p EXP n divides CARD (group_carrier G)
     ==> ?K:A->bool.
           K subgroup_of G /\
           CARD K = p EXP n`;;

let SYLOW_IS_PRETRANSITIVE_OF_FINITE =
  `let is_p_subgroup =
     \(G:A group) (p:num) (H:A->bool).
       H subgroup_of G /\
       pgroup {p} (subgroup_generated G H) in
   let is_sylow =
     \(G:A group) (p:num) (P:A->bool).
       is_p_subgroup G p P /\
       !Q:A->bool.
         is_p_subgroup G p Q /\ P SUBSET Q ==> Q = P in
   !G:A group. !p:num.
     prime p /\
     FINITE {P:A->bool | is_sylow G p P}
     ==> !P Q:A->bool.
           is_sylow G p P /\
           is_sylow G p Q
           ==> group_conjugate G P Q`;;

let SYLOW_CARD_DVD_INDEX =
  `let is_p_subgroup =
     \(G:A group) (p:num) (H:A->bool).
       H subgroup_of G /\
       pgroup {p} (subgroup_generated G H) in
   let is_sylow =
     \(G:A group) (p:num) (P:A->bool).
       is_p_subgroup G p P /\
       !Q:A->bool.
         is_p_subgroup G p Q /\ P SUBSET Q ==> Q = P in
   let subgroup_index =
     \(G:A group) (P:A->bool).
       let cosets =
         {left_coset G x P | x | x IN group_carrier G} in
       if FINITE cosets then CARD cosets else 0 in
   !G:A group. !p:num. !P:A->bool.
     prime p /\
     FINITE {Q:A->bool | is_sylow G p Q} /\
     is_sylow G p P
     ==> CARD {Q:A->bool | is_sylow G p Q}
         divides subgroup_index G P`;;

let CARD_SYLOW_MODEQ_ONE =
  `let is_p_subgroup =
     \(G:A group) (p:num) (H:A->bool).
       H subgroup_of G /\
       pgroup {p} (subgroup_generated G H) in
   let is_sylow =
     \(G:A group) (p:num) (P:A->bool).
       is_p_subgroup G p P /\
       !Q:A->bool.
         is_p_subgroup G p Q /\ P SUBSET Q ==> Q = P in
   !G:A group. !p:num.
     prime p /\
     FINITE {P:A->bool | is_sylow G p P}
     ==> (CARD {P:A->bool | is_sylow G p P} == 1) (mod p)`;;
