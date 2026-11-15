(*
  Statement-only formalization of PutnamBench artifact putnam_1978_a2:
  the determinant formula for a real square matrix with constant entries
  above and below the diagonal and arbitrary diagonal entries. This file
  contains no proof.
*)

let determinants_output = open_out "/dev/null";;
let determinants_formatter =
  Format.formatter_of_out_channel determinants_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file determinants_formatter path);;
let determinants_loaded =
  Toploop.use_file determinants_formatter "Multivariate/determinants.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush determinants_formatter ();;
close_out determinants_output;;
if not determinants_loaded then
  failwith "failed to load Multivariate/determinants.ml";;

let statement =
  `!n:num. !a b:real. !c:num->real. !A:real^N^N. !p:real->real.
     dimindex(:N) = n /\
     0 < n /\
     ~(a = b) /\
     A = ((lambda i j.
            if i < j then a else if i > j then b else c i):real^N^N) /\
     p = (\x. product (1..n) (\i. c i - x))
     ==> det A = (b * p a - a * p b) / (b - a)`;;
