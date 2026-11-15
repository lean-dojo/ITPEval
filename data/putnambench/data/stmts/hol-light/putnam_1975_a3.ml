(*
  Statement-only formalization of PutnamBench artifact putnam_1975_a3:
  the explicit points where a sum of real powers attains its maximum and
  minimum on a nonnegative real-power level set. This file contains no proof.
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
  `let rpow =
     \x p:real. if x = &0 then &0 else exp (p * ln x) in
   !a b c:real.
     &0 < a /\ a < b /\ b < c
     ==>
     let xmax = rpow (a / b) (&1 / (b - a)) in
     let ymax = rpow (&1 - rpow xmax b) (&1 / b) in
     let zmin = rpow (b / c) (&1 / (c - b)) in
     let ymin = rpow (&1 - rpow zmin b) (&1 / b) in
     let feasible =
       \x y z:real.
         &0 <= x /\ &0 <= y /\ &0 <= z /\
         rpow x b + rpow y b + rpow z b = &1 in
     let objective =
       \x y z:real. rpow x a + rpow y b + rpow z c in
     (feasible xmax ymax (&0) /\
      (!x y z:real.
         feasible x y z
         ==> objective x y z <= objective xmax ymax (&0))) /\
     (feasible (&0) ymin zmin /\
      (!x y z:real.
         feasible x y z
         ==> objective x y z >= objective (&0) ymin zmin))`;;
