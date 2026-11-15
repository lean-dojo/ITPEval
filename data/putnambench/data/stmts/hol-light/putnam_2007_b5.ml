(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_b5:
  existence, for every positive integer k, of k real polynomials expressing
  the kth power of floor(n/k) for every integer n. This file contains no proof.
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
  `!k:num.
     0 < k
     ==> ?P:num->real->real.
           (!i:num. i < k ==> polynomial_function (P i)) /\
           !n:int.
             (floor (real_of_int n / &k)) pow k =
             sum (0..k - 1)
               (\i:num.
                  P i (real_of_int n) *
                  (floor (real_of_int n / &k)) pow i)`;;
