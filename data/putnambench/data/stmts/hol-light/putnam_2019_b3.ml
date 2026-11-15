(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_b3
  (putnambench__hol-light__putnam_2019_b3): a real orthogonal matrix without
  eigenvalue 1 acquires eigenvalue 1 after left multiplication by the
  reflection determined by a unit vector. This file contains no proof.
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
  `!n:num. !Q P:real^N^N. !u:real^N.
     0 < n /\
     dimindex(:N) = n /\
     orthogonal_matrix Q /\
     u dot u = &1 /\
     P = mat 1 - &2 %% (lambda i j. u$i * u$j)
     ==>
     (~(det (Q - mat 1) = &0)
      ==> det (P ** Q - mat 1) = &0)`;;
