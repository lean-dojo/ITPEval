(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_b1:
  evaluation of a finite sum of minima of distances from two rational
  multiples to the nearest integers. This file contains no proof.
*)

let floor_output = open_out "/dev/null";;
let floor_formatter = Format.formatter_of_out_channel floor_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file floor_formatter path);;
let floor_loaded =
  Toploop.use_file floor_formatter "Library/floor.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush floor_formatter ();;
close_out floor_output;;
if not floor_loaded then failwith "failed to load Library/floor.ml";;

let statement =
  `let dist_to_int =
     \x:real. min (x - floor x) (floor (x + &1) - x) in
   !n:num.
     0 < n
     ==>
     sum (1..6 * n - 1)
       (\m:num.
          min (dist_to_int (&m / (&6 * &n)))
              (dist_to_int (&m / (&3 * &n)))) =
     &n`;;
