(*
  Statement-only formalization of PutnamBench artifact putnam_1982_b2:
  evaluation of a Gaussian-weighted double integral of the integer lattice
  point counting function in terms of its Gaussian series. This file contains
  no proof.
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
         ==> ?B:real.
               !t:real. B <= t ==> abs (f t - l) < e in
   let whole_integral =
     \(f:real->real).
       @l:real.
         tends_at_posinfinity
           (\t:real. integral(--t,t) f)
           l in
   let A =
     \(x:real) (y:real).
       CARD
         {(m,n):int#int |
            real_of_int (m pow 2 + n pow 2) <= x pow 2 + y pow 2} in
   let g =
     suminf (\n:num. exp (--(&n pow 2))) in
   let I =
     whole_integral
       (\x:real.
          whole_integral
            (\y:real.
               &(A x y) * exp (--(x pow 2) - y pow 2))) in
   I = pi * (&2 * g - &1) pow 2`;;
