(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1065966,
  "Isomorphism theorem": the first, second, and third isomorphism theorems for
  quotient groups. This file contains no proof.
*)

let isomorphism_theorem_output = open_out "/dev/null";;
let isomorphism_theorem_formatter =
  Format.formatter_of_out_channel isomorphism_theorem_output;;
let previous_file_loader = !Hol_loader.file_loader;;
let previous_verbose = !verbose;;
let previous_type_invention_warning = !type_invention_warning;;
verbose := false;;
type_invention_warning := false;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file isomorphism_theorem_formatter path);;
let isomorphism_theorem_library_loaded =
  Toploop.use_file isomorphism_theorem_formatter "Library/grouptheory.ml";;
Hol_loader.file_loader := previous_file_loader;;
verbose := previous_verbose;;
type_invention_warning := previous_type_invention_warning;;
Format.pp_print_flush isomorphism_theorem_formatter ();;
close_out isomorphism_theorem_output;;
if not isomorphism_theorem_library_loaded then
  failwith "failed to load Library/grouptheory.ml";;

let QUOTIENT_GROUP_QUOTIENT_KER_EQUIV_RANGE =
  `!G H (f:A->B).
     group_homomorphism (G,H) f
     ==> quotient_group G (group_kernel (G,H) f) isomorphic_group
         subgroup_generated H (group_image (G,H) f)`;;

let QUOTIENT_GROUP_QUOTIENT_INF_EQUIV_PROD_NORMAL_QUOTIENT =
  `!G (H:A->bool) N.
     H subgroup_of G /\
     N normal_subgroup_of G
     ==> quotient_group (subgroup_generated G H) (H INTER N)
         isomorphic_group
         quotient_group
           (subgroup_generated G (group_setmul G H N)) N`;;

let QUOTIENT_GROUP_QUOTIENT_QUOTIENT_EQUIV_QUOTIENT =
  `!G (N:A->bool) M.
     N normal_subgroup_of G /\
     M normal_subgroup_of G /\
     N SUBSET M
     ==> quotient_group
           (quotient_group G N)
           (IMAGE (right_coset G N) M)
         isomorphic_group
         quotient_group G M`;;
