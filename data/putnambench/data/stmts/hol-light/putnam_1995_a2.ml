(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_a2:
  classification of the positive real pairs for which the specified improper
  integral of nested square-root differences converges. This file contains no
  proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let tends_at_posinfinity =
     \(g:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?B:real.
               !t:real. B <= t ==> abs (g t - l) < e in
   !a b:real.
     &0 < a /\ &0 < b
     ==>
     ((?l:real.
         tends_at_posinfinity
           (\t:real.
              integral(b,t)
                (\x:real.
                   sqrt (sqrt (x + a) - sqrt x) -
                   sqrt (sqrt x - sqrt (x - b))))
           l)
      <=> a = b)`;;
