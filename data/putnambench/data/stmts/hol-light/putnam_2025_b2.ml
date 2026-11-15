(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b2
  (putnambench__hol-light__putnam_2025_b2): comparison of the normalized first
  moments weighted by a nonnegative continuous strictly increasing function
  on the unit interval and by its square. This file contains no proof.
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
  `let continuous_on_unit_interval =
     \(f:real->real).
       !x:real.
         &0 <= x /\ x <= &1
         ==> !e:real.
               &0 < e
               ==> ?d:real.
                     &0 < d /\
                     !y:real.
                       &0 <= y /\ y <= &1 /\ abs (y - x) < d
                       ==> abs (f y - f x) < e in
   !f:real->real.
     continuous_on_unit_interval f /\
     (!x y:real.
        &0 <= x /\ x <= &1 /\
        &0 <= y /\ y <= &1 /\
        x < y
        ==> f x < f y) /\
     (!x:real. &0 <= x /\ x <= &1 ==> &0 <= f x)
     ==>
     integral(&0,&1) (\x:real. x * f x) / integral(&0,&1) f <
     integral(&0,&1) (\x:real. x * (f x) pow 2) /
     integral(&0,&1) (\x:real. (f x) pow 2)`;;
