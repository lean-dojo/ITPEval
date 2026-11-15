(*
  Statement-only formalization of Thousand Theorems corpus artifact Q505798,
  "Lagrange's theorem (group theory)": the natural cardinal of every subgroup
  divides the natural cardinal of its ambient group, with natural cardinal
  zero for infinite carriers. This file contains no proof.
*)

let q505798_output = open_out "/dev/null";;
let q505798_formatter = Format.formatter_of_out_channel q505798_output;;
let q505798_previous_file_loader = !Hol_loader.file_loader;;
let q505798_previous_verbose = !verbose;;
let q505798_previous_type_invention_warning = !type_invention_warning;;
verbose := false;;
type_invention_warning := false;;
Format.pp_print_flush Format.std_formatter ();;
Format.pp_set_formatter_out_channel Format.std_formatter q505798_output;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q505798_formatter path);;
let q505798_library_loaded =
  Toploop.use_file q505798_formatter "Library/grouptheory.ml";;
Hol_loader.file_loader := q505798_previous_file_loader;;
verbose := q505798_previous_verbose;;
type_invention_warning := q505798_previous_type_invention_warning;;
Format.pp_print_flush Format.std_formatter ();;
Format.pp_set_formatter_out_channel Format.std_formatter stdout;;
Format.pp_print_flush q505798_formatter ();;
close_out q505798_output;;
if not q505798_library_loaded then
  failwith "failed to load Library/grouptheory.ml";;

let Q505798_LAGRANGE_S_THEOREM_GROUP_THEORY =
  `let natural_cardinal =
     \S:A->bool. if FINITE S then CARD S else 0 in
   !G:A group. !H:A->bool.
     H subgroup_of G
     ==> natural_cardinal H divides natural_cardinal (group_carrier G)`;;
