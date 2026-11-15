(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_a6:
  a continuous real-valued function on the real plane whose integral over
  every axis-aligned rectangle of area one is zero must vanish identically.
  This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let continuous_on_plane =
     \(f:(real#real)->real).
       !x y e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !u v:real.
                 sqrt ((u - x) pow 2 + (v - y) pow 2) < d
                 ==> abs (f (u,v) - f (x,y)) < e in
   let putnam_2012_a6_solution = T in
   !p:((real#real)->real)->bool.
     (!f:(real#real)->real.
        p f <=>
        continuous_on_plane f /\
        (!x1 x2 y1 y2:real.
           x1 < x2 /\
           y1 < y2 /\
           (x2 - x1) * (y2 - y1) = &1
           ==>
           integral(x1,x2)
             (\x:real.
                integral(y1,y2)
                  (\y:real. f (x,y))) = &0))
     ==>
     ((!f:(real#real)->real. !x y:real.
         p f ==> f (x,y) = &0) <=>
      putnam_2012_a6_solution)`;;
