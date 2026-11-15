(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_a3:
  the classification of real polynomials whose ordered roots have derivative
  zeros at every adjacent midpoint. This file contains no proof.
*)

let poly_output = open_out "/dev/null";;
let poly_formatter = Format.formatter_of_out_channel poly_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file poly_formatter path);;
let poly_loaded =
  Toploop.use_file poly_formatter "Library/poly.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush poly_formatter ();;
close_out poly_output;;
if not poly_loaded then failwith "failed to load Library/poly.ml";;

let statement =
  `let putnam_1991_a3_solution =
     \p:real list.
       degree p = 2 /\
       (?r1 r2:real.
          ~(r1 = r2) /\
          poly p r1 = &0 /\
          poly p r2 = &0) in
   !p:real list n:num.
     n = degree p /\
     2 <= n
     ==>
     ((?r:num->real.
         (!i:num.
            i < n - 1
            ==> r i < r (i + 1)) /\
         (!i:num.
            i < n
            ==> poly p (r i) = &0) /\
         (!i:num.
            i < n - 1
            ==> poly (poly_diff p) ((r i + r (i + 1)) / &2) = &0))
      <=> putnam_1991_a3_solution p)`;;
