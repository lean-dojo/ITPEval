(*
  Statement-only formalization of PutnamBench artifact putnam_1969_b6:
  real rectangular matrices whose specified product is a fixed symmetric
  three-by-three matrix, forcing the reverse product to be nine times the
  two-by-two identity matrix. This file contains no proof.
*)

let vectors_output = open_out "/dev/null";;
let vectors_formatter = Format.formatter_of_out_channel vectors_output;;
let vectors_loaded =
  Toploop.use_file vectors_formatter "Multivariate/vectors.ml";;
Format.pp_print_flush vectors_formatter ();;
close_out vectors_output;;
if not vectors_loaded then failwith "failed to load Multivariate/vectors.ml";;

let statement =
  `!(A:real^2^3) (B:real^3^2) (p:real^3^3).
     p$1$1 = &8 /\ p$1$2 = &2 /\ p$1$3 = -- &2 /\
     p$2$1 = &2 /\ p$2$2 = &5 /\ p$2$3 = &4 /\
     p$3$1 = -- &2 /\ p$3$2 = &4 /\ p$3$3 = &5 /\
     A ** B = p
     ==> B ** A = mat 9`;;
