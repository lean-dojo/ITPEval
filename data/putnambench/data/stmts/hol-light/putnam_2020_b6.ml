(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_b6
  (putnambench__hol-light__putnam_2020_b6): nonnegativity of an alternating
  finite sum whose exponents are floors of multiples of sqrt(2) - 1. This
  file contains no proof.
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
  `!n:num.
     0 < n
     ==>
     sum (1..n)
       (\k:num.
          (--(&1):real) zpow
          (int_of_real (floor (&k * (sqrt(&2) - &1))))) >=
     &0`;;
