(*
  Statement-only formalization of Thousand Theorems corpus artifact Q288465,
  "Orbit-stabilizer theorem": for a group action and a point, its orbit is
  bijective with the left-coset space of its stabilizer. This file contains
  no proof.
*)

let q288465_output = open_out "/dev/null";;
let q288465_formatter = Format.formatter_of_out_channel q288465_output;;
let q288465_previous_file_loader = !Hol_loader.file_loader;;
let q288465_previous_verbose = !verbose;;
let q288465_previous_type_invention_warning = !type_invention_warning;;
verbose := false;;
type_invention_warning := false;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q288465_formatter path);;
let q288465_library_loaded =
  Toploop.use_file q288465_formatter "Library/grouptheory.ml";;
Hol_loader.file_loader := q288465_previous_file_loader;;
verbose := q288465_previous_verbose;;
type_invention_warning := q288465_previous_type_invention_warning;;
Format.pp_print_flush q288465_formatter ();;
close_out q288465_output;;
if not q288465_library_loaded then
  failwith "failed to load Library/grouptheory.ml";;

let Q288465_ORBIT_STABILIZER_THEOREM =
  `!(G:A group) (action:A->B->B) (b:B).
     group_action G (:B) action
     ==> group_orbit G (:B) action b =_c
         {left_coset G g (group_stabilizer G action b) |g|
          g IN group_carrier G}`;;
