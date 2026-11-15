(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_a1:
  for a positive integer k, the numerator polynomial in the nth derivative of
  1 / (x^k - 1) evaluates at 1 to (-k)^n n!. This file contains no proof.
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
     \(g:real->real) (x:real).
       if g differentiable x
       then (@d:real. (g diffl d) x)
       else &0 in
   !k:num.
   !P:num->real->real.
     0 < k /\
     (!n:num. polynomial_function (P n)) /\
     (!n:num. !x:real.
        ITER n deriv (\x':real. &1 / (x' pow k - &1)) x =
        P n x / ((x pow k - &1) pow (n + 1)))
     ==>
     !n:num.
       P n (&1) = (--(&k)) pow n * &(FACT n)`;;
