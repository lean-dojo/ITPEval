(*
  Statement-only formalization of PutnamBench artifact putnam_1980_a6:
  the greatest uniform lower bound of the integral of |f' - f| over [0,1]
  for continuously differentiable real functions with f(0)=0 and f(1)=1 is
  1 / exp(1). This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let interval = {x:real | &0 <= x /\ x <= &1} in
   let has_derivative_within =
     \(f:real->real) (d:real) (x:real).
       !e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real.
                 y IN interval /\
                 &0 < abs (y - x) /\
                 abs (y - x) < delta
                 ==> abs ((f y - f x) / (y - x) - d) < e in
   let derivative_on =
     \(f:real->real) (x:real).
       @d:real. has_derivative_within f d x in
   let continuous_on =
     \(g:real->real).
       !x:real.
         x IN interval
         ==> !e:real.
               &0 < e
               ==> ?delta:real.
                     &0 < delta /\
                     !y:real.
                       y IN interval /\ abs (y - x) < delta
                       ==> abs (g y - g x) < e in
   let class_c =
     \(f:real->real).
       (!x:real.
          x IN interval
          ==> has_derivative_within f (derivative_on f x) x) /\
       continuous_on (derivative_on f) /\
       f (&0) = &0 /\
       f (&1) = &1 in
   let admissible =
     \u:real.
       !f:real->real.
         class_c f
         ==> u <=
             integral(&0,&1)
               (\x. abs (derivative_on f x - f x)) in
   admissible (&1 / exp (&1)) /\
   (!u:real. admissible u ==> u <= &1 / exp (&1))`;;
