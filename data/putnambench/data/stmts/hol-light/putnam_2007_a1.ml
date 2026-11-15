(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_a1:
  classification of the real coefficients alpha for which the curves
  y = alpha*x^2 + alpha*x + 1/24 and x = alpha*y^2 + alpha*y + 1/24 are
  tangent to each other. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let deriv =
     \(f:real->real) (x:real).
       if f differentiable x
       then @d:real. (f diffl d) x
       else &0 in
   let putnam_2007_a1_solution =
     {a:real |
        a = &2 / &3 \/
        a = &3 / &2 \/
        a = (&13 + sqrt(&601)) / &12 \/
        a = (&13 - sqrt(&601)) / &12} in
   !P:(real->real)->bool. !a:real.
     (!f:real->real.
        P f <=>
        ?x y:real.
          f x = y /\
          f y = x /\
          deriv f x * deriv f y = &1)
     ==>
     (P (\t:real. a * t pow 2 + a * t + &1 / &24) <=>
      a IN putnam_2007_a1_solution)`;;
