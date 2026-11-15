(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_a2:
  for f(x) = exp(x^2), there is an open real interval and a nonzero
  differentiable function g on which (f * g)' = f' * g'. This file contains
  no proof.
*)

let transc_output = open_out "/dev/null";;
let transc_formatter = Format.formatter_of_out_channel transc_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file transc_formatter path);;
let transc_loaded =
  Toploop.use_file transc_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush transc_formatter ();;
close_out transc_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let deriv =
     \(h:real->real) (x:real). @d. (h diffl d) x in
   let f = \x:real. exp (x pow 2) in
   let putnam_1988_a2_solution = T in
   (?a b:real.
      a < b /\
      ?g:real->real.
        (?x:real. a < x /\ x < b /\ ~(g x = &0)) /\
        (!x:real. a < x /\ x < b ==> g differentiable x) /\
        (!x:real.
           a < x /\ x < b
           ==> deriv (\y:real. f y * g y) x =
               deriv f x * deriv g x))
   <=> putnam_1988_a2_solution`;;
