(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1983_b5:
  the limiting normalized integral of the distance from n/x to the nearest
  integer, assuming Wallis' product formula. This file contains no proof.
*)

let library_output = open_out "/dev/null";;
let library_formatter = Format.formatter_of_out_channel library_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file library_formatter path);;
let floor_loaded =
  Toploop.use_file library_formatter "Library/floor.ml";;
let transc_loaded =
  Toploop.use_file library_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush library_formatter ();;
close_out library_output;;
if not floor_loaded then failwith "failed to load Library/floor.ml";;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let mindist =
     \x:real. min (x - floor x) (floor (x + &1) - x) in
   ((\N:num.
       product (1..N)
         (\n:num.
            ((&2 * &n) / (&2 * &n - &1)) *
            ((&2 * &n) / (&2 * &n + &1))))
    tends_num_real (pi / &2))
   ==>
   (\n:num.
      (&1 / &n) *
      integral(&1,&n) (\x:real. mindist (&n / x)))
   tends_num_real (ln (&4 / pi))`;;
