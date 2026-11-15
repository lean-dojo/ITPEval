(*
  Statement-only formalization of PutnamBench artifact putnam_1963_a3:
  the integral formula for an n-th order Euler differential equation with
  zero initial derivatives at 1. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file analysis_formatter path);;
let transc_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
let iter_loaded =
  Toploop.use_file analysis_formatter "Library/iter.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;
if not iter_loaded then failwith "failed to load Library/iter.ml";;

let statement =
  `let domain = {x:real | &1 <= x} in
   let continuous_on =
     \(g:real->real) (s:real->bool).
       !x. x IN s
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !x'. x' IN s /\ abs (x' - x) < d
                                ==> abs (g x' - g x) < e in
   let deriv =
     \(g:real->real) (x:real). @d. (g diffl d) x in
   let solution =
     \(f:real->real) (n:num) (x:real) (t:real).
       (x - t) pow (n - 1) * f t /
       (&(FACT (n - 1)) * t pow n) in
   !P:num->(real->real)->(real->real).
   !n:num. !f y:real->real.
     P 0 = (\u. u) /\
     (!i:num. !u:real->real.
        P (SUC i) u =
        P i (\x. x * deriv u x - &i * u x)) /\
     0 < n /\
     continuous_on f domain /\
     (!k. k < n
          ==> (!x. x IN domain
                   ==> (ITER k deriv y) differentiable x) /\
              continuous_on (ITER (SUC k) deriv y) domain)
     ==>
     (((!k. k < n ==> ITER k deriv y (&1) = &0) /\
       (!x. &1 <= x ==> P n y x = f x)) <=>
      (!x. &1 <= x
           ==> y x =
               integral(&1,x) (solution f n x)))`;;
