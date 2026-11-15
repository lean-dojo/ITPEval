(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1187646,
  "Fundamental theorem on homomorphisms": the quotient of a group by the
  kernel of a homomorphism is isomorphic to its range. This file contains no
  proof.
*)

let fundamental_homomorphism_theorem_output = open_out "/dev/null";;
let fundamental_homomorphism_theorem_formatter =
  Format.formatter_of_out_channel fundamental_homomorphism_theorem_output;;
let previous_file_loader = !Hol_loader.file_loader;;
let previous_verbose = !verbose;;
let previous_type_invention_warning = !type_invention_warning;;
verbose := false;;
type_invention_warning := false;;
Hol_loader.file_loader :=
  (fun path ->
     Toploop.use_file fundamental_homomorphism_theorem_formatter path);;
let fundamental_homomorphism_theorem_library_loaded =
  Toploop.use_file
    fundamental_homomorphism_theorem_formatter "Library/grouptheory.ml";;
Hol_loader.file_loader := previous_file_loader;;
verbose := previous_verbose;;
type_invention_warning := previous_type_invention_warning;;
Format.pp_print_flush fundamental_homomorphism_theorem_formatter ();;
close_out fundamental_homomorphism_theorem_output;;
if not fundamental_homomorphism_theorem_library_loaded then
  failwith "failed to load Library/grouptheory.ml";;

let Q1187646_FUNDAMENTAL_THEOREM_ON_HOMOMORPHISMS =
  `!G H (f:A->B).
     group_homomorphism (G,H) f
     ==> quotient_group G (group_kernel (G,H) f) isomorphic_group
         subgroup_generated H (group_image (G,H) f)`;;
