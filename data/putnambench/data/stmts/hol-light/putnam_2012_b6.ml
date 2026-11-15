(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_b6:
  parity of the cube permutation of residue classes modulo an odd prime
  congruent to 2 modulo 3, characterized by congruence to 3 modulo 4.
  This file contains no proof.
*)

let permutations_output = open_out "/dev/null";;
let permutations_formatter =
  Format.formatter_of_out_channel permutations_output;;
let previous_file_loader = !Hol_loader.file_loader;;
let previous_verbose = !verbose;;
let previous_report_timing = !report_timing;;
verbose := false;;
report_timing := false;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file permutations_formatter path);;
let permutations_loaded =
  Toploop.use_file permutations_formatter "Library/permutations.ml";;
Hol_loader.file_loader := previous_file_loader;;
verbose := previous_verbose;;
report_timing := previous_report_timing;;
Format.pp_print_flush permutations_formatter ();;
close_out permutations_output;;
if not permutations_loaded then
  failwith "failed to load Library/permutations.ml";;

let statement =
  `!p:num. !P:num->num.
     ODD p /\
     prime p /\
     p MOD 3 = 2 /\
     P permutes {i:num | i < p} /\
     (!i:num. i < p ==> P i = (i EXP 3) MOD p)
     ==>
     (evenperm P <=> p MOD 4 = 3)`;;
