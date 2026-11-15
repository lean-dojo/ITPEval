(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527189,
  "Lattice theorem": Noether's third isomorphism theorem for groups, identifying
  (G / N) / (M / N) with G / M when N and M are normal and N is contained in M.
  This file contains no proof.
*)

let q3527189_output = open_out "/dev/null";;
let q3527189_formatter = Format.formatter_of_out_channel q3527189_output;;
let q3527189_previous_file_loader = !Hol_loader.file_loader;;
let q3527189_previous_verbose = !verbose;;
let q3527189_previous_type_invention_warning = !type_invention_warning;;
verbose := false;;
type_invention_warning := false;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q3527189_formatter path);;
let q3527189_library_loaded =
  Toploop.use_file q3527189_formatter "Library/grouptheory.ml";;
Hol_loader.file_loader := q3527189_previous_file_loader;;
verbose := q3527189_previous_verbose;;
type_invention_warning := q3527189_previous_type_invention_warning;;
Format.pp_print_flush q3527189_formatter ();;
close_out q3527189_output;;
if not q3527189_library_loaded then
  failwith "failed to load Library/grouptheory.ml";;

let Q3527189_LATTICE_THEOREM =
  `!G (N:A->bool) M.
     N normal_subgroup_of G /\
     M normal_subgroup_of G /\
     N SUBSET M
     ==> quotient_group
           (quotient_group G N)
           (IMAGE (right_coset G N) M)
         isomorphic_group
         quotient_group G M`;;
