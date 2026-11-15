(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_a5:
  real polynomials whose values at 1 through n are the counterclockwise
  vertices of a regular n-gon have degree at least n - 1 in one coordinate.
  This file contains no proof.
*)

let complex_transc_output = open_out "/dev/null";;
let complex_transc_formatter =
  Format.formatter_of_out_channel complex_transc_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file complex_transc_formatter path);;
let complex_transc_loaded =
  Toploop.use_file complex_transc_formatter "Complex/complex_transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush complex_transc_formatter ();;
close_out complex_transc_output;;
if not complex_transc_loaded then
  failwith "failed to load Complex/complex_transc.ml";;

let statement =
  `let eval_poly =
     \(p:real list) (x:real).
       ITLIST (\a acc. a + x * acc) p (&0) in
   let degree_at_least =
     \(p:real list) (d:num).
       ?j:num.
         d <= j /\
         j < LENGTH p /\
         ~(EL j p = &0) in
   !n:num. !f g:real list.
     3 <= n /\
     (?center z:complex.
        ~(z = Cx(&0)) /\
        (!k:num.
           k IN (1..n)
           ==>
           Cx(eval_poly f (&k)) + ii * Cx(eval_poly g (&k)) =
           center + z * cexp(ii * Cx(&2 * pi * &k / &n))))
     ==>
     degree_at_least f (n - 1) \/ degree_at_least g (n - 1)`;;
