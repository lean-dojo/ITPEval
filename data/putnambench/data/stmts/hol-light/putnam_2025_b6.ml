(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b6
  (putnambench__hol-light__putnam_2025_b6): the greatest real exponent for
  which a positive-integer-valued function can satisfy the stated iterated
  growth inequality is 1/4. This file contains no proof.
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
  `let rpow =
     \x r:real. exp (r * ln x) in
   let admissible =
     \r:real.
       ?g:num->num.
         (!n:num. 0 < n ==> 0 < g n) /\
         (!n:num.
            0 < n
            ==>
            rpow (&(g (g n))) r
            <= &(g (n + 1)) - &(g n)) in
   admissible (&1 / &4) /\
   (!r:real. admissible r ==> r <= &1 / &4)`;;
