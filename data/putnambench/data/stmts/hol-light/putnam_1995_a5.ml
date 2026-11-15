(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_a5:
  linear dependence of finite families of differentiable real solutions of a
  positive-coefficient constant linear differential system that vanish at
  positive infinity. This file contains no proof.
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
     \(f:real->real) (t:real). @d:real. (f diffl d) t in
   let tends_at_posinfinity =
     \(f:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?B:real.
               !t:real. B <= t ==> abs (f t - l) < e in
   let putnam_1995_a5_solution = T in
   putnam_1995_a5_solution <=>
   (!n:num. !x:num->real->real. !a:num->num->real.
      0 < n /\
      (!i:num. i < n ==> !t:real. (x i) differentiable t) /\
      (!i j:num. i < n /\ j < n ==> &0 < a i j) /\
      (!t:real. !i:num.
         i < n
         ==> deriv (x i) t =
             sum (0..n - 1) (\j:num. a i j * x j t)) /\
      (!i:num. i < n ==> tends_at_posinfinity (x i) (&0))
      ==>
      ~(!b:num->real.
          (!t:real.
             sum (0..n - 1) (\i:num. b i * x i t) = &0)
          ==>
          (!i:num. i < n ==> b i = &0)))`;;
