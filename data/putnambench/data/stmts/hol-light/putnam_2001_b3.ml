(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_b3:
  evaluation as 3 of the infinite series formed from powers of 2 indexed by
  the nearest integer to each positive integer's square root. This file
  contains no proof.
*)

let library_output = open_out "/dev/null";;
let library_formatter = Format.formatter_of_out_channel library_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file library_formatter path);;
let floor_loaded =
  Toploop.use_file library_formatter "Library/floor.ml";;
let analysis_loaded =
  Toploop.use_file library_formatter "Library/analysis.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush library_formatter ();;
close_out library_output;;
if not floor_loaded then failwith "failed to load Library/floor.ml";;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let closest =
     \n:num.
       num_of_int
         (int_of_real (floor (sqrt (&(n + 1)) + &1 / &2))) in
   (\n:num.
      ((&2:real) pow (closest n) +
       &1 / ((&2:real) pow (closest n))) /
      ((&2:real) pow (n + 1)))
   sums (&3)`;;
