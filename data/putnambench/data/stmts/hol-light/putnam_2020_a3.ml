(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_a3
  (putnambench__hol-light__putnam_2020_a3): divergence of the sum of squares
  of the recursively defined sequence starting at pi/2 and iterating sine.
  This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let putnam_2020_a3_solution = F in
   !a:num->real.
     a 0 = pi / &2 /\
     (!n:num. a (n + 1) = sin (a n))
     ==>
     ((?L:real.
         (\m:num. sum (1..m) (\n:num. (a n) pow 2))
         tends_num_real L)
      <=>
      putnam_2020_a3_solution)`;;
