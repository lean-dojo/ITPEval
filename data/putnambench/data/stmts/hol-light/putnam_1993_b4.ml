(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1993_b4:
  positive continuous real functions and a positive continuous kernel on the
  unit interval satisfying reciprocal integral equations are equal there.
  This file contains no proof.
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
  `let unit_interval = {x:real | &0 <= x /\ x <= &1} in
   let continuous_on_interval =
     \(h:real->real).
       !x:real.
         x IN unit_interval
         ==> !e:real.
               &0 < e
               ==> ?d:real.
                     &0 < d /\
                     !y:real.
                       y IN unit_interval /\ abs (y - x) < d
                       ==> abs (h y - h x) < e in
   let continuous_on_rectangle =
     \(K:(real#real)->real).
       !x y:real.
         x IN unit_interval /\ y IN unit_interval
         ==> !e:real.
               &0 < e
               ==> ?d:real.
                     &0 < d /\
                     !x' y':real.
                       x' IN unit_interval /\
                       y' IN unit_interval /\
                       abs (x' - x) < d /\
                       abs (y' - y) < d
                       ==> abs (K (x',y') - K (x,y)) < e in
   !K:(real#real)->real. !f g:real->real.
     ((!x y:real.
         x IN unit_interval /\ y IN unit_interval
         ==> &0 < K (x,y)) /\
      continuous_on_rectangle K /\
      (!x:real.
         x IN unit_interval
         ==> &0 < f x /\ &0 < g x) /\
      continuous_on_interval f /\
      continuous_on_interval g /\
      (!x:real.
         x IN unit_interval
         ==> integral(&0,&1) (\y:real. f y * K (x,y)) = g x /\
             integral(&0,&1) (\y:real. g y * K (x,y)) = f x))
     ==>
     !x:real. x IN unit_interval ==> f x = g x`;;
