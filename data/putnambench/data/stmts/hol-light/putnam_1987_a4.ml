(*
  Statement-only formalization of PutnamBench artifact putnam_1987_a4:
  the distance from one coordinate of a complex zero of a real-coefficient
  trivariate polynomial satisfying a scaling identity and three specified
  values. This file contains no proof.
*)

let cpoly_output = open_out "/dev/null";;
let cpoly_formatter = Format.formatter_of_out_channel cpoly_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file cpoly_formatter path);;
let cpoly_loaded =
  Toploop.use_file cpoly_formatter "Complex/cpoly.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush cpoly_formatter ();;
close_out cpoly_output;;
if not cpoly_loaded then failwith "failed to load Complex/cpoly.ml";;

let statement =
  `let eval3 =
     \P:((complex list)list)list.
       \x y z:complex.
         poly
           (MAP
             (\q:(complex list)list.
                poly (MAP (\p:complex list. poly p x) q) y)
             P)
           z in
   let real_coefficients =
     \P:((complex list)list)list.
       !q p a.
         MEM q P /\ MEM p q /\ MEM a p
         ==> Im a = &0 in
   let putnam_1987_a4_solution = (&5 / &3) * sqrt(&30) in
   !P:((complex list)list)list.
   !f:real->real->real.
   !A B C:complex.
     real_coefficients P /\
     (!x y z u:real.
        eval3 P (Cx(u * x)) (Cx(u * y)) (Cx(u * z)) =
        Cx(u pow 2 * f (y - x) (z - x))) /\
     eval3 P (Cx(&1)) (Cx(&0)) (Cx(&0)) = Cx(&4) /\
     eval3 P (Cx(&0)) (Cx(&1)) (Cx(&0)) = Cx(&5) /\
     eval3 P (Cx(&0)) (Cx(&0)) (Cx(&1)) = Cx(&6) /\
     eval3 P A B C = Cx(&0) /\
     norm (B - A) = &10
     ==> norm (C - A) = putnam_1987_a4_solution`;;
