(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_a3:
  the exponent -1 and positive limit 2/pi for a ratio of sine- and
  cosine-weighted real-power integrals as the exponent tends to positive
  infinity. This file contains no proof.
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
               !r:real. B <= r ==> abs (g r - l) < e in
   let rpow =
     \x p:real. if x = &0 then &0 else exp (p * ln x) in
   let putnam_2011_a3_solution = (-- &1,&2 / pi) in
   let c = FST putnam_2011_a3_solution in
   let L = SND putnam_2011_a3_solution in
   &0 < L /\
   tends_at_posinfinity
     (\r:real.
        (rpow r c *
         integral(&0,pi / &2)
           (\x:real. rpow x r * sin x)) /
        integral(&0,pi / &2)
          (\x:real. rpow x r * cos x))
     L`;;
