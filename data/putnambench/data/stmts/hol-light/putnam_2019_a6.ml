(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_a6
  (putnambench__hol-light__putnam_2019_a6): a dichotomy for a twice
  differentiable real function with faster-than-x^r decay at zero, between
  decay of its first derivative and unbounded scaled second derivative.
  This file contains no proof.
*)

let transc_output = open_out "/dev/null";;
let transc_formatter = Format.formatter_of_out_channel transc_output;;
let previous_file_loader = !Hol_loader.file_loader;;
let previous_verbose = !verbose;;
let previous_type_invention_warning = !type_invention_warning;;
verbose := false;;
type_invention_warning := false;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file transc_formatter path);;
let transc_loaded =
  Toploop.use_file transc_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
verbose := previous_verbose;;
type_invention_warning := previous_type_invention_warning;;
Format.pp_print_flush transc_formatter ();;
close_out transc_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let deriv =
     \(f:real->real) (x:real). @d:real. (f diffl d) x in
   let rpow =
     \x r:real. exp (r * ln x) in
   let continuous_on_closed_unit =
     \g:real->real.
       !x:real.
         &0 <= x /\ x <= &1
         ==> !e:real.
               &0 < e
               ==> ?d:real.
                     &0 < d /\
                     !y:real.
                       &0 <= y /\ y <= &1 /\ abs (y - x) < d
                       ==> abs (g y - g x) < e in
   let tends_to_at_right_zero =
     \(f:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !x:real.
                 &0 < x /\ x < d ==> abs (f x - l) < e in
   let twice_differentiable_on_open_unit =
     \g:real->real.
       !x:real.
         &0 < x /\ x < &1
         ==> g differentiable x /\ deriv g differentiable x in
   let scaled_second_derivative_unbounded_at_zero =
     \g:real->real. \r:real.
       !B:real.
         ?d:real.
           &0 < d /\
           !x:real.
             &0 < x /\ x < d
             ==> ?x':real.
                   &0 < x' /\ x' <= x /\
                   B <
                   rpow x' r *
                   abs (deriv (deriv g) x') in
   !g:real->real. !r:real.
     continuous_on_closed_unit g /\
     twice_differentiable_on_open_unit g /\
     &1 < r /\
     tends_to_at_right_zero (\x:real. g x / rpow x r) (&0)
     ==>
     tends_to_at_right_zero (deriv g) (&0) \/
     scaled_second_derivative_unbounded_at_zero g r`;;
