(*
  Statement-only formalization of PutnamBench artifact putnam_1977_b3:
  eventual balancing of positive irrational real triples under the specified
  coordinatewise doubling map, with the answer false. This file contains no
  proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let iter_loaded =
  Toploop.use_file analysis_formatter "Library/iter.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not iter_loaded then failwith "failed to load Library/iter.ml";;

let statement =
  `let is_rational =
     \x:real.
       ?p q:int.
         ~(q = (&0:int)) /\
         x = real_of_int p / real_of_int q in
   let P =
     \(a,b,c):real#real#real.
       ~is_rational a /\
       ~is_rational b /\
       ~is_rational c /\
       &0 < a /\
       &0 < b /\
       &0 < c /\
       a + b + c = &1 in
   let balanced =
     \(a,b,c):real#real#real.
       a < &1 / &2 /\
       b < &1 / &2 /\
       c < &1 / &2 in
   let B =
     \(a,b,c):real#real#real.
       ((if a > &1 / &2 then &2 * a - &1 else &2 * a),
        (if b > &1 / &2 then &2 * b - &1 else &2 * b),
        (if c > &1 / &2 then &2 * c - &1 else &2 * c)) in
   let putnam_1977_b3_solution = F in
   ((!t:real#real#real.
       P t ==> ?n:num. balanced (ITER n B t)) <=>
    putnam_1977_b3_solution)`;;
