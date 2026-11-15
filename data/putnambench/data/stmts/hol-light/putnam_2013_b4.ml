(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_b4:
  the variance of the product of two continuous real functions on the unit
  interval is bounded using their variances and maximum absolute values.
  This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let unit_interval = {x:real | &0 <= x /\ x <= &1} in
   let continuous_on =
     \(f:real->real) (s:real->bool).
       !x. x IN s
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !y. y IN s /\ abs (y - x) < d
                               ==> abs (f y - f x) < e in
   let mean =
     \(f:real->real). integral(&0,&1) f in
   let variance =
     \(f:real->real).
       integral(&0,&1) (\x. (f x - mean f) pow 2) in
   let max_abs =
     \(f:real->real).
       sup (IMAGE (\x. abs (f x)) unit_interval) in
   !f g:real->real.
     continuous_on f unit_interval /\
     continuous_on g unit_interval
     ==>
     variance (\x. f x * g x)
     <= &2 * variance f * (max_abs g) pow 2 +
        &2 * variance g * (max_abs f) pow 2`;;
