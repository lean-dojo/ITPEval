(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_a2:
  the determinant of the n by n real matrix whose (i,j)-entry is the
  reciprocal of min(i,j). This file contains no proof.
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
  `!n:num. !A:real^N^N.
     0 < n /\
     dimindex(:N) = n /\
     (!i j:num.
        i IN 1..n /\ j IN 1..n
        ==> A$i$j = &1 / &(MIN i j))
     ==> det A =
         (-- &1) pow (n - 1) /
         (&(FACT (n - 1)) * &(FACT n))`;;
