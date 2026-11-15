(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_b2
  (putnambench__hol-light__putnam_2019_b2): the limit of a normalized finite
  trigonometric sum is 8 divided by the cube of pi. This file contains no
  proof.
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
  `let a =
     \n:num.
       sum (1..n - 1)
         (\k:num.
            sin ((&2 * &k - &1) * pi / (&2 * &n)) /
            ((cos ((&k - &1) * pi / (&2 * &n))) pow 2 *
             (cos (&k * pi / (&2 * &n))) pow 2)) in
   (\n:num. a n / (&n) pow 3)
   tends_num_real
   (&8 / pi pow 3)`;;
