(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_a3
  (putnambench__hol-light__putnam_2016_a3): the functional equation involving
  the principal real arctangent determines the integral of f on [0,1] as
  3*pi/8. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `!f:real->real.
     (!x:real.
        ~(x = &0)
        ==> f x + f (&1 - &1 / x) = atn x)
     ==> integral(&0,&1) f = &3 * pi / &8`;;
