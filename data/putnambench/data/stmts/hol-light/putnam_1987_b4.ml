(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_b4:
  convergence to -1 and 0 of the two real sequences defined by the given
  trigonometric recurrence. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let putnam_1987_b4_solution = (T,--(&1:real),T,(&0:real)) in
   let existsx = FST putnam_1987_b4_solution in
   let limx = FST (SND putnam_1987_b4_solution) in
   let existsy = FST (SND (SND putnam_1987_b4_solution)) in
   let limy = SND (SND (SND putnam_1987_b4_solution)) in
   !x y:num->real.
     (x 1 = &4 / &5 /\
      y 1 = &3 / &5 /\
      (!n:num.
         1 <= n
         ==> x (n + 1) =
             x n * cos (y n) - y n * sin (y n)) /\
      (!n:num.
         1 <= n
         ==> y (n + 1) =
             x n * sin (y n) + y n * cos (y n)))
     ==>
     (((?c:real. x tends_num_real c) ==> existsx) /\
      (existsx ==> x tends_num_real limx) /\
      ((?c:real. y tends_num_real c) ==> existsy) /\
      (existsy ==> y tends_num_real limy))`;;
