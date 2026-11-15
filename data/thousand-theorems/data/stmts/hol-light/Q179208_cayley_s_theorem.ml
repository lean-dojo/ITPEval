(*
  Statement-only formalization of Thousand Theorems corpus artifact Q179208,
  "Cayley's theorem": a group acting faithfully on a type is isomorphic, via
  its action representation, to the corresponding subgroup of the symmetric
  group. This file contains no proof.
*)

let q179208_output = open_out "/dev/null";;
let q179208_formatter = Format.formatter_of_out_channel q179208_output;;
let q179208_previous_file_loader = !Hol_loader.file_loader;;
let q179208_previous_verbose = !verbose;;
let q179208_previous_type_invention_warning = !type_invention_warning;;
verbose := false;;
type_invention_warning := false;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q179208_formatter path);;
let q179208_library_loaded =
  Toploop.use_file q179208_formatter "Library/symmetric_group.ml";;
Hol_loader.file_loader := q179208_previous_file_loader;;
verbose := q179208_previous_verbose;;
type_invention_warning := q179208_previous_type_invention_warning;;
Format.pp_print_flush q179208_formatter ();;
close_out q179208_output;;
if not q179208_library_loaded then
  failwith "failed to load Library/symmetric_group.ml";;

let Q179208_CAYLEY_S_THEOREM =
  `!(G:A group) (action:A->B->B).
     group_action G (:B) action /\
     (!g h.
        g IN group_carrier G /\
        h IN group_carrier G /\
        (!x:B. action g x = action h x)
        ==> g = h)
     ==> group_isomorphism
           (G,
            subgroup_generated
              (symmetric_group (:B))
              (group_image (G,symmetric_group (:B)) action))
           action`;;
