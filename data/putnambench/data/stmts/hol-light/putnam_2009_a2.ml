(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_a2:
  the explicit local solution for the first component of a three-function
  nonlinear differential system with initial values at zero. This file
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
  `let rpow =
     \x p:real. if x = &0 then &0 else exp (p * ln x) in
   let deriv =
     \(u:real->real) (x:real). @d:real. (u diffl d) x in
   let putnam_2009_a2_solution =
     \x:real.
       rpow (&2) (--(&1) / &12) *
       rpow
         (sin (&6 * x + pi / &4) /
          (cos (&6 * x + pi / &4)) pow 2)
         (&1 / &6) in
   !f g h:real->real. !a b:real.
     a < &0 /\ &0 < b /\
     (!x:real. a < x /\ x < b ==> f differentiable x) /\
     (!x:real. a < x /\ x < b ==> g differentiable x) /\
     (!x:real. a < x /\ x < b ==> h differentiable x) /\
     (!x:real. a < x /\ x < b
          ==> deriv f x =
              &2 * (f x) pow 2 * g x * h x +
              &1 / (g x * h x)) /\
     f (&0) = &1 /\
     (!x:real. a < x /\ x < b
          ==> deriv g x =
              f x * (g x) pow 2 * h x +
              &4 / (f x * h x)) /\
     g (&0) = &1 /\
     (!x:real. a < x /\ x < b
          ==> deriv h x =
              &3 * f x * g x * (h x) pow 2 +
              &1 / (f x * g x)) /\
     h (&0) = &1
     ==>
     ?c d:real.
       c < &0 /\ &0 < d /\
       !x:real. c < x /\ x < d
                ==> f x = putnam_2009_a2_solution x`;;
