(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1983_a6:
  convergence to 2/9 at positive infinity of a scaled iterated integral of
  exp(x^3 + y^3) over a right triangle. This file contains no proof.
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
               !a:real. B <= a ==> abs (g a - l) < e in
   let putnam_1983_a6_solution = &2 / &9 in
   tends_at_posinfinity
     (\a:real.
        (a pow 4 / exp (a pow 3)) *
        integral(&0,a)
          (\x:real.
             integral(&0,a - x)
               (\y:real. exp (x pow 3 + y pow 3))))
     putnam_1983_a6_solution`;;
