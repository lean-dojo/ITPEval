(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_b4:
  for every positive integer n, every complex root of the polynomial whose
  coefficient of z^k is 2^(k*(n-k)) is real. This file contains no proof.
*)

let cpoly_output = open_out "/dev/null";;
let cpoly_formatter = Format.formatter_of_out_channel cpoly_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file cpoly_formatter path);;
let cpoly_loaded =
  Toploop.use_file cpoly_formatter "Complex/cpoly.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush cpoly_formatter ();;
close_out cpoly_output;;
if not cpoly_loaded then failwith "failed to load Complex/cpoly.ml";;

let statement =
  `!n:num.
     0 < n
     ==>
     !z:complex.
       poly
         (list_of_seq
           (\k:num. Cx(&(2 EXP (k * (n - k)))))
           (n + 1))
         z =
       Cx(&0)
       ==> Im z = &0`;;
