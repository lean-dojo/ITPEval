(*
  Statement-only formalization of PutnamBench artifact putnam_1962_b6:
  the extremal form of a nonconstant real trigonometric polynomial bounded
  by one and attaining unit absolute value at 2n points. This file contains
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
  `!n:num. !a b:num->real. !xs:real->bool. !f:real->real.
     f =
       (\x. sum (0..n)
                (\k. a k * sin (&k * x) +
                     b k * cos (&k * x))) /\
     (!x. &0 <= x /\ x <= &2 * pi ==> abs (f x) <= &1) /\
     xs HAS_SIZE (2 * n) /\
     xs SUBSET {x | &0 <= x /\ x < &2 * pi} /\
     (!x. x IN xs ==> abs (f x) = &1)
     ==> (~(?c:real. f = (\x. c))
          ==> ?alpha:real. f = (\x. cos (&n * x + alpha)))`;;
