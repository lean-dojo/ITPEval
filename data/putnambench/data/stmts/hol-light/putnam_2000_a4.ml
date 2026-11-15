(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_a4:
  convergence of the improper integral from zero to positive infinity of
  sin(x) times sin(x squared). This file contains no proof.
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
  `let tends_at_posinfinity =
     \(f:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?A:real.
               !B:real. A <= B ==> abs (f B - l) < e in
   ?y:real.
     tends_at_posinfinity
       (\B:real.
          integral(&0,B)
            (\x:real. sin x * sin(x pow 2)))
       y`;;
