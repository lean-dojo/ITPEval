(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_b4:
  the smallest possible numerator degree after differentiating a rational
  function with denominator x^3 - x exactly 1992 times is 3984. This file
  contains no proof.
*)

let poly_output = open_out "/dev/null";;
let poly_formatter = Format.formatter_of_out_channel poly_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file poly_formatter path);;
let poly_loaded =
  Toploop.use_file poly_formatter "Library/poly.ml";;
let iter_loaded =
  Toploop.use_file poly_formatter "Library/iter.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush poly_formatter ();;
close_out poly_output;;
if not poly_loaded then failwith "failed to load Library/poly.ml";;
if not iter_loaded then failwith "failed to load Library/iter.ml";;

let statement =
  `let deriv =
     \(h:real->real) (x:real).
       if ?d:real. (h diffl d) x
       then @d:real. (h diffl d) x
       else &0 in
   let x3_minus_x:real list = [&0; -- &1; &0; &1] in
   let valid =
     \p:real list.
       ~(poly p = poly []) /\
       degree p < 1992 /\
       (!d:real list.
          poly_divides d p /\ poly_divides d x3_minus_x
          ==> degree d = 0) in
   let pair =
     \(p:real list) (f:real list).
       ?g:real list.
         ~(poly g = poly []) /\
         !x:real.
           ~(x = -- &1) /\ ~(x = &0) /\ ~(x = &1) /\
           ~(poly g x = &0)
           ==>
           (ITER 1992 deriv
              (\y:real. poly p y / (y pow 3 - y))) x =
           poly f x / poly g x in
   let feasible =
     \k:num.
       ?p f:real list.
         valid p /\ pair p f /\ k = degree f in
   let putnam_1992_b4_solution = 3984 in
   feasible putnam_1992_b4_solution /\
   (!k:num. feasible k ==> putnam_1992_b4_solution <= k)`;;
