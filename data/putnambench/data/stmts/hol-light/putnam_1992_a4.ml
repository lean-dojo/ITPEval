(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_a4:
  the derivatives at zero of an infinitely differentiable real function
  prescribed at reciprocal positive integers. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file analysis_formatter path);;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
let iter_loaded =
  Toploop.use_file analysis_formatter "Library/iter.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;
if not iter_loaded then failwith "failed to load Library/iter.ml";;

let statement =
  `let deriv =
     \(g:real->real) (x:real). @d. (g diffl d) x in
   let infinitely_differentiable =
     \(g:real->real).
       !k:num. !x:real. (ITER k deriv g) differentiable x in
   let putnam_1992_a4_solution =
     \k:num.
       if EVEN k
       then (-- &1) pow (k DIV 2) * &(FACT k)
       else &0 in
   !f:real->real.
     infinitely_differentiable f /\
     (!n:num.
        0 < n
        ==> f (&1 / &n) =
            (&n pow 2) / (&n pow 2 + &1))
     ==>
     !k:num.
       0 < k
       ==> ITER k deriv f (&0) =
           putnam_1992_a4_solution k`;;
