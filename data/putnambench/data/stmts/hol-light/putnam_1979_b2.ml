(*
  Statement-only formalization of PutnamBench artifact putnam_1979_b2:
  the limit at zero of a real-power integral mean of a positive affine
  function on the unit interval. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let rpow =
     \x p:real. if x = &0 then &0 else exp (p * ln x) in
   let solution =
     \a b:real.
       exp (-- &1) *
       rpow (rpow b b / rpow a a) (&1 / (b - a)) in
   !a b:real.
     &0 < a /\ a < b
     ==>
     ((\t.
         rpow
           (integral(&0,&1)
              (\x. rpow (b * x + a * (&1 - x)) t))
           (&1 / t))
      --> solution a b)
     (&0)`;;
