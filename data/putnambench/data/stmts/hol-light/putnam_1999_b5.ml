(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_b5:
  the determinant of the identity plus the n by n cosine matrix whose
  entries use all pairwise sums of one-based angular multiples. This file
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

needs "Library/transc.ml";;

let statement =
  `!n:num. !theta:real. !A:real^N^N.
     3 <= n /\
     dimindex(:N) = n /\
     theta = &2 * pi / &n /\
     A = ((lambda j k.
            cos (&j * theta + &k * theta)):real^N^N)
     ==> det (mat 1 + A) = &1 - (&n pow 2) / &4`;;
