(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_b2:
  an integral bound for a continuously differentiable real function on the
  unit interval with zero integral. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let in_domain = \x:real. &0 <= x /\ x <= &1 in
   let has_derivative_on =
     \(f:real->real) (d:real) (x:real).
       !e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real.
                 in_domain y /\
                 ~(y = x) /\
                 abs (y - x) < delta
                 ==> abs ((f y - f x) / (y - x) - d) < e in
   let continuous_on =
     \(g:real->real).
       !x:real.
         in_domain x
         ==> !e:real.
               &0 < e
               ==> ?delta:real.
                     &0 < delta /\
                     !y:real.
                       in_domain y /\ abs (y - x) < delta
                       ==> abs (g y - g x) < e in
   !f:real->real. !m:real.
     ((?f':real->real.
         (!x:real.
            in_domain x ==> has_derivative_on f (f' x) x) /\
         continuous_on f' /\
         (?x:real. in_domain x /\ abs (f' x) = m) /\
         (!x:real. in_domain x ==> abs (f' x) <= m)) /\
      integral(&0,&1) f = &0)
     ==>
     !a:real.
       &0 < a /\ a < &1
       ==> abs (integral(&0,a) f) <= (&1 / &8) * m`;;
