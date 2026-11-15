(*
  Statement-only formalization of PutnamBench artifact putnam_1978_a3:
  among the integrals over the nonnegative real line of x^k divided by the
  specified degree-six polynomial, the value for k = 2 is least for natural
  k from 1 through 4. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let tends_at_posinfinity =
     \(g:real->real) (r:real).
       !e:real.
         &0 < e
         ==> ?B:real.
               !b:real. B <= b ==> abs (g b - r) < e in
   let improper_integral =
     \(f:real->real).
       @r:real.
         tends_at_posinfinity
           (\b:real. integral(&0,b) f)
           r in
   let p =
     \x:real.
       &2 * (x pow 6 + &1) +
       &4 * (x pow 5 + x) +
       &3 * (x pow 4 + x pow 2) +
       &5 * x pow 3 in
   let I =
     \k:num.
       improper_integral (\x. x pow k / p x) in
   let putnam_1978_a3_solution = 2 in
   1 <= putnam_1978_a3_solution /\
   putnam_1978_a3_solution <= 4 /\
   (!k:num.
      1 <= k /\ k <= 4
      ==> I putnam_1978_a3_solution <= I k)`;;
