(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2226800,
  "Schur-Zassenhaus theorem": a normal subgroup whose order is coprime to its
  index has a complementary subgroup giving unique factorization of every
  group element. This file contains no proof.
*)

let schur_zassenhaus_output = open_out "/dev/null";;
let schur_zassenhaus_formatter =
  Format.formatter_of_out_channel schur_zassenhaus_output;;
let previous_file_loader = !Hol_loader.file_loader;;
let previous_verbose = !verbose;;
let previous_type_invention_warning = !type_invention_warning;;
verbose := false;;
type_invention_warning := false;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file schur_zassenhaus_formatter path);;
let schur_zassenhaus_library_loaded =
  Toploop.use_file schur_zassenhaus_formatter "Library/grouptheory.ml";;
Hol_loader.file_loader := previous_file_loader;;
verbose := previous_verbose;;
type_invention_warning := previous_type_invention_warning;;
Format.pp_print_flush schur_zassenhaus_formatter ();;
close_out schur_zassenhaus_output;;
if not schur_zassenhaus_library_loaded then
  failwith "failed to load Library/grouptheory.ml";;

let Q2226800_SCHUR_ZASSENHAUS_THEOREM =
  `let subgroup_order =
     \H:A->bool. if FINITE H then CARD H else 0 in
   let subgroup_index =
     \(G:A group) (N:A->bool).
       let left_cosets =
         {left_coset G x N | x | x IN group_carrier G} in
       if FINITE left_cosets then CARD left_cosets else 0 in
   !G:A group. !N:A->bool.
     N normal_subgroup_of G /\
     coprime(subgroup_order N,subgroup_index G N)
     ==> ?H:A->bool.
           H subgroup_of G /\
           !g:A.
             g IN group_carrier G
             ==> ?!p:A#A.
                   FST p IN H /\
                   SND p IN N /\
                   group_mul G (FST p) (SND p) = g`;;
