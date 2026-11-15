(*
  Statement-only formalization of PutnamBench artifact putnam_1972_a3:
  the supercontinuous real functions on the unit interval, defined by
  preservation of Cesaro convergence, are exactly the affine functions there.
  This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let climit_exists =
     \x:num->real.
       ?C:real.
         (\n:num. sum (0..n - 1) x / &n) tends_num_real C in
   let supercontinuous =
     \f:real->real.
       !x:num->real.
         (!i:num. &0 <= x i /\ x i <= &1)
         ==> climit_exists x
         ==> climit_exists (\i:num. f (x i)) in
   !f:real->real.
     supercontinuous f <=>
     ?A B:real.
       !x:real.
         &0 <= x /\ x <= &1
         ==> f x = A * x + B`;;
