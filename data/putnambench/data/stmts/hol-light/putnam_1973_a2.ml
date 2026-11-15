(*
  Statement-only formalization of PutnamBench artifact putnam_1973_a2:
  convergence of a harmonic series with an eight-term periodic sign pattern,
  and the necessity and sufficiency of having four positive signs per block.
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
  `let putnam_1973_a2_solution = T in
   !L:real list. !pluses:num. !S:num->real.
     LENGTH L = 8 /\
     (!i:num.
        i < LENGTH L
        ==> EL i L = &1 \/ EL i L = -- &1) /\
     pluses = CARD {i:num | i < LENGTH L /\ EL i L = &1} /\
     S = (\n:num. sum (1..n) (\i:num. EL (i MOD 8) L / &i))
     ==>
     ((pluses = 4 ==> ?l:real. S tends_num_real l) /\
      (putnam_1973_a2_solution <=>
       ((?l:real. S tends_num_real l) ==> pluses = 4)))`;;
