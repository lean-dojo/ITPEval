(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_a3:
  evaluation of an improper integral of the product of two specified real
  power series as the square root of e. This file contains no proof.
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
   let series1 =
     \x:real.
       suminf
         (\n:num.
            (-- &1) pow n * x pow (2 * n + 1) /
            &(2 EXP n * FACT n)) in
   let series2 =
     \x:real.
       suminf
         (\n:num.
            x pow (2 * n) /
            (&(2 EXP n * FACT n) pow 2)) in
   tends_at_posinfinity
     (\t:real.
        integral(&0,t)
          (\x:real. series1 x * series2 x))
     (sqrt (exp (&1)))`;;
