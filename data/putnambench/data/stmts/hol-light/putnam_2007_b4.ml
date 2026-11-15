(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_b4:
  the number of ordered pairs of real polynomials whose squares sum to
  X^(2n) + 1 and whose degrees are strictly decreasing. This file contains
  no proof.
*)

let poly_output = open_out "/dev/null";;
let poly_formatter = Format.formatter_of_out_channel poly_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file poly_formatter path);;
let poly_loaded =
  Toploop.use_file poly_formatter "Library/poly.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush poly_formatter ();;
close_out poly_output;;
if not poly_loaded then failwith "failed to load Library/poly.ml";;

let statement =
  `!n:num.
     0 < n
     ==>
     CARD
       {pq:(real list)#(real list) |
          let p = FST pq in
          let q = SND pq in
          normalize p = p /\
          normalize q = q /\
          degree p > degree q /\
          (!x:real.
             (poly p x) pow 2 + (poly q x) pow 2 =
             x pow (2 * n) + &1)} =
     2 EXP (n + 1)`;;
