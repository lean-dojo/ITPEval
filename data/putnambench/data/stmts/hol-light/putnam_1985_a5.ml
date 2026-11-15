(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_a5:
  classification of the integers from 1 through 10 for which the integral
  over 0 to 2 pi of a finite product of cosines is nonzero. This file contains
  no proof.
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
  `!m:num.
     1 <= m /\ m <= 10
     ==>
     (~(integral(&0,&2 * pi)
          (\x:real. product (1..m) (\k:num. cos (&k * x))) = &0)
      <=>
      m = 3 \/ m = 4 \/ m = 7 \/ m = 8)`;;
