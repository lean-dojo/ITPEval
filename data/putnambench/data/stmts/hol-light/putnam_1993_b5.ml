(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_b5:
  four points in the Euclidean plane cannot have all six pairwise distances
  be odd integers. This file contains no proof.
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
  `let odd_integer_distance =
     \x:real.
       ?n:int.
         x = real_of_int n /\
         ?k:int. n = &2 * k + &1 in
   ~(?point0 point1 point2 point3:real^2.
       odd_integer_distance (dist(point0,point1)) /\
       odd_integer_distance (dist(point0,point2)) /\
       odd_integer_distance (dist(point0,point3)) /\
       odd_integer_distance (dist(point1,point2)) /\
       odd_integer_distance (dist(point1,point3)) /\
       odd_integer_distance (dist(point2,point3)))`;;
