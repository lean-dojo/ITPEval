(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_a1:
  a maximum-area triangle with vertices on the positive branch of xy = 1
  cuts off equal areas between the hyperbola and its two adjacent chords.
  This file contains no proof.
*)

let transc_output = open_out "/dev/null";;
let transc_formatter = Format.formatter_of_out_channel transc_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file transc_formatter path);;
let transc_loaded =
  Toploop.use_file transc_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush transc_formatter ();;
close_out transc_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let hyperbola =
     \p:real^2. p$2 = &1 / p$1 /\ &0 < p$1 in
   let triangle_area =
     \U V W:real^2.
       abs ((V$1 - U$1) * (W$2 - U$2) -
            (V$2 - U$2) * (W$1 - U$1)) / &2 in
   let region_area =
     \U V:real^2.
       (V$1 - U$1) * (U$2 + V$2) / &2 -
       (log(V$1) - log(U$1)) in
   !A B P:real^2.
     hyperbola A /\
     hyperbola B /\
     A$1 < B$1 /\
     hyperbola P /\
     A$1 < P$1 /\
     P$1 < B$1 /\
     (!P':real^2.
        hyperbola P' /\ A$1 < P'$1 /\ P'$1 < B$1
        ==> triangle_area A P' B <= triangle_area A P B)
     ==>
     region_area A P = region_area P B`;;
