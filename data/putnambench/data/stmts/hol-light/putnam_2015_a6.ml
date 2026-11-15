(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_a6:
  determinant equality for intertwined real square matrices with the same
  characteristic polynomial. This file contains no proof.
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
  `!n:num. !A B M:real^N^N.
     0 < n /\
     dimindex(:N) = n /\
     A ** M = M ** B /\
     (!x:real.
        det (x %% mat 1 - A) = det (x %% mat 1 - B))
     ==>
     !X:real^N^N.
       det (A - M ** X) = det (B - X ** M)`;;
