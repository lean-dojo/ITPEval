(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_a5:
  evaluation of the sum-to-product ratio of tangent values at equally spaced
  angles for a positive odd integer. This file contains no proof.
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
  `let is_rational =
     \x:real.
       ?p q:int.
         ~(q = &0) /\
         x = real_of_int p / real_of_int q in
   let putnam_2006_a5_solution =
     \n:num.
       if n MOD 4 = 1 then (&n:real) else --(&n) in
   !n:num. !theta:real. !a:num->real.
     ODD n /\
     ~is_rational (theta / pi) /\
     (!k:num.
        k IN (1..n)
        ==> a k = tan (theta + &k * pi / &n))
     ==>
     sum (1..n) a / product (1..n) a =
     putnam_2006_a5_solution n`;;
