(*
  Statement-only formalization of PutnamBench artifact putnam_1975_b2:
  a convergent sum of positive slab thicknesses cannot cover all of
  three-dimensional Euclidean space. This file contains no proof.
*)

let vectors_output = open_out "/dev/null";;
let vectors_formatter = Format.formatter_of_out_channel vectors_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file vectors_formatter path);;
let vectors_loaded =
  Toploop.use_file vectors_formatter "Multivariate/vectors.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush vectors_formatter ();;
close_out vectors_output;;
if not vectors_loaded then failwith "failed to load Multivariate/vectors.ml";;

let statement =
  `!slab:real^3->real->real->real^3->bool.
   !normals:num->real^3.
   !offsets thicknesses:num->real.
     slab =
       (\normal offset thickness.
          {x:real^3 |
             offset < normal dot x /\
             normal dot x < offset + thickness}) /\
     (!i:num. norm (normals i) = &1) /\
     (!i:num. &0 < thicknesses i) /\
     (?C:real.
        !e:real.
          &0 < e
          ==> ?N:num.
                !n:num.
                  N <= n
                  ==> abs
                        (sum {j:num | j < n} thicknesses - C) < e)
     ==> ~((UNIV:real^3->bool) =
           UNIONS
             (IMAGE
               (\i:num.
                  slab (normals i) (offsets i) (thicknesses i))
               (:num)))`;;
