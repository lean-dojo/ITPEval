(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_a3
  (putnambench__hol-light__putnam_2019_a3): the greatest universal lower bound
  for the average modulus of the roots of a degree-2019 polynomial with
  strictly increasing real coefficients from 1 to 2019. This file contains no
  proof.
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
  `let admissible =
     \b:real list.
       LENGTH b = 2020 /\
       &1 <= EL 0 b /\
       EL 2019 b <= &2019 /\
       (!k:num. k < 2019 ==> EL k b < EL (k + 1) b) in
   let root_list =
     \b:real list.
     \zs:complex list.
       LENGTH zs = 2019 /\
       (!z:complex.
          poly (MAP Cx b) z =
          Cx (EL 2019 b) *
          ITLIST (\w acc:complex. (z - w) * acc) zs (Cx(&1))) in
   let average_modulus =
     \zs:complex list.
       sum (0..2018) (\i:num. norm (EL i zs)) / &2019 in
   let lower_bound =
     \M:real.
       !b:real list. !zs:complex list.
         admissible b /\ root_list b zs
         ==> M <= average_modulus zs in
   let putnam_2019_a3_solution = &1 / root 2019 (&2019) in
   lower_bound putnam_2019_a3_solution /\
   (!M:real.
      lower_bound M ==> M <= putnam_2019_a3_solution)`;;
