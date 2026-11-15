(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_b5
  (putnambench__hol-light__putnam_2016_b5): classification of functions from
  (1,infinity) to itself that preserve the interval between the square and
  cube of each input. This file contains no proof.
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
     \x c:real. exp (c * ln x) in
   !f:real->real.
     ((!x:real. &1 < x ==> &1 < f x) /\
      (!x y:real.
         &1 < x /\ &1 < y /\
         x pow 2 <= y /\ y <= x pow 3
         ==>
         (f x) pow 2 <= f y /\ f y <= (f x) pow 3))
     <=>
     (?c:real.
        &0 < c /\
        (!x:real. &1 < x ==> f x = rpow x c))`;;
