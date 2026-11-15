(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_a2:
  the determinant of the intersection matrix indexed by all nonempty subsets
  of {1,...,n}. This file contains no proof.
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
  `!n:num. !S:num->num->bool. !M:real^N^N.
     1 <= n /\
     dimindex(:N) = 2 EXP n - 1 /\
     IMAGE S (1..dimindex(:N)) =
       {U:num->bool | U SUBSET (1..n) /\ ~(U = {})} /\
     (!i j:num.
        i IN 1..dimindex(:N) /\ j IN 1..dimindex(:N)
        ==> M$i$j = if S i INTER S j = {} then &0 else &1)
     ==> det M = (if n = 1 then &1 else -- &1)`;;
