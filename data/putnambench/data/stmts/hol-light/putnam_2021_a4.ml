(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_a4
  (putnambench__hol-light__putnam_2021_a4): the limit at positive infinity
  of a two-dimensional rational-function integral over a disk. This file
  contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let integrand =
     \(x:real) (y:real).
       (&1 + &2 * x pow 2) /
       (&1 + x pow 4 + &6 * x pow 2 * y pow 2 + y pow 4) -
       (&1 + y pow 2) /
       (&2 + x pow 4 + y pow 4) in
   let I =
     \R:real.
       integral(--(abs R),abs R)
         (\x:real.
            integral
              (--(sqrt (R pow 2 - x pow 2)),
               sqrt (R pow 2 - x pow 2))
              (\y:real. integrand x y)) in
   let tends_at_posinfinity =
     \(f:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?B:real.
               !R:real.
                 B <= R ==> abs (f R - l) < e in
   tends_at_posinfinity
     I
     ((sqrt (&2) / &2) * pi * ln (&2))`;;
