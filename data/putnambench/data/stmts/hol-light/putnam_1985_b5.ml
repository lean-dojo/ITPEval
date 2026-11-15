(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_b5:
  evaluation of an improper integral involving a negative half power and an
  exponential reciprocal term, assuming the Gaussian integral. This file
  contains no proof.
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
     \(g:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?B:real.
               !b:real. B <= b ==> abs (g b - l) < e in
   let rpow =
     \x p:real. if x = &0 then &0 else exp (p * ln x) in
   let gaussian_integral =
     tends_at_posinfinity
       (\b:real.
          integral(--b,b) (\x:real. exp (--(x pow 2))))
       (sqrt pi) in
   let putnam_1985_b5_solution =
     sqrt (pi / &1985) * exp (-- &3970) in
   gaussian_integral
   ==>
   tends_at_posinfinity
     (\b:real.
        integral(&0,b)
          (\t:real.
             rpow t (--(&1 / &2)) *
             exp
               (--(&1985 *
                    (t + rpow t (-- &1))))))
     putnam_1985_b5_solution`;;
