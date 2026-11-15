(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_b3:
  moments of a rapidly decaying function satisfying a dilation differential
  equation, including their formula and normalized convergence. This file
  contains no proof.
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
               !b:real. B <= b ==> abs (g b - l) < e in
   let differentiable_on =
     \(g:real->real) (s:real->bool).
       !a:real.
         a IN s
         ==> ?d:real.
               !e:real.
                 &0 < e
                 ==> ?delta:real.
                       &0 < delta /\
                       !y:real.
                         y IN s /\
                         &0 < abs (y - a) /\
                         abs (y - a) < delta
                         ==> abs ((g y - g a) / (y - a) - d) < e in
   let moment =
     \(g:real->real) (n:num) (r:real).
       tends_at_posinfinity
         (\b:real. integral(&0,b) (\x:real. x pow n * g x))
         r in
   let putnam_1989_b3_solution =
     \n:num. \c:real.
       c * &(FACT n) /
       ((&3) pow n *
        product (1..n) (\m:num. &1 - inv ((&2) pow m))) in
   !f:real->real. !mu:num->real.
     differentiable_on f {x:real | &0 <= x} /\
     (!x:real.
        &0 < x
        ==> (f diffl (-- &3 * f x + &6 * f (&2 * x))) x) /\
     (!x:real. &0 <= x ==> abs (f x) <= exp (--(sqrt x))) /\
     (!n:num. moment f n (mu n))
     ==>
     (!n:num. mu n = putnam_1989_b3_solution n (mu 0)) /\
     (?L:real.
        (\n:num. mu n * (&3) pow n / &(FACT n)) tends_num_real L) /\
     (((\n:num. mu n * (&3) pow n / &(FACT n)) tends_num_real &0)
      ==> mu 0 = &0)`;;
