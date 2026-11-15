(*
  Statement-only formalization of PutnamBench artifact putnam_1973_b2:
  rationality of the distance from one of every even integer power of a unit
  complex number with rational components, together with the reciprocal
  modulus formulation for nonnegative powers. This file contains no proof.
*)

let complex_output = open_out "/dev/null";;
let complex_formatter = Format.formatter_of_out_channel complex_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file complex_formatter path);;
let complex_loaded =
  Toploop.use_file complex_formatter "Complex/complexnumbers.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush complex_formatter ();;
close_out complex_output;;
if not complex_loaded then
  failwith "failed to load Complex/complexnumbers.ml";;

let statement =
  `let is_rational =
     \x:real.
       ?p q:int.
         ~(q = (&0:int)) /\
         x = real_of_int p / real_of_int q in
   let integer_power =
     \(z:complex) (n:int).
       if (&0:int) <= n
       then z pow (num_of_int n)
       else inv (z pow (num_of_int (--n))) in
   !z:complex.
     is_rational (Re z) /\
     is_rational (Im z) /\
     norm z = &1
     ==>
     (!n:int.
        is_rational
          (norm
            (integer_power z ((&2:int) * n) - Cx(&1)))) /\
     (!n:num.
        is_rational
          (norm
            (inv (z pow (2 * n) - Cx(&1)))))`;;
