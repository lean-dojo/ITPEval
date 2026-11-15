(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_b3:
  the closed-form value of the 2007th term of a recurrence involving the
  floor of sqrt(5) times the preceding term. This file contains no proof.
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
  `let a = (&1 + sqrt(&5)) / &2 in
   !x:num->real.
     (x 0 = &1 /\
      (!n:num.
         x (n + 1) =
         &3 * x n + floor (x n * sqrt(&5))))
     ==>
     x 2007 =
     ((&2:real) pow 2006 / sqrt(&5)) *
     (a pow 4017 + a zpow (--(&4017:int)))`;;
