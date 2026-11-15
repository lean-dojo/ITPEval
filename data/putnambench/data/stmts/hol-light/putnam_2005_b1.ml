(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_b1:
  existence of a nonzero real bivariate polynomial that vanishes at
  (floor a, floor (2 * a)) for every real number a. This file contains no
  proof.
*)

let library_output = open_out "/dev/null";;
let library_formatter = Format.formatter_of_out_channel library_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file library_formatter path);;
let floor_loaded =
  Toploop.use_file library_formatter "Library/floor.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush library_formatter ();;
close_out library_output;;
if not floor_loaded then failwith "failed to load Library/floor.ml";;

let statement =
  `(?x y:real.
      ~((y - &2 * x) * (y - &2 * x - &1) = &0)) /\
   (!a:real.
      let x = floor a in
      let y = floor (&2 * a) in
      (y - &2 * x) * (y - &2 * x - &1) = &0)`;;
