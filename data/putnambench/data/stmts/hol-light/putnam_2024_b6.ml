(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_b6
  (putnambench__hol-light__putnam_2024_b6): the threshold real exponent for
  the left-hand asymptotics at 1 of an exponentially weighted power series.
  The threshold is -1/2. This file contains no proof.
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
     \u a:real. exp (a * ln u) in
   let tends_at_left =
     \(f:real->real) (b:real) (l:real).
       !e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !x:real.
                 x < b /\ abs (x - b) < d
                 ==> abs (f x - l) < e in
   let tends_at_left_posinfinity =
     \(f:real->real) (b:real).
       !M:real.
         ?d:real.
           &0 < d /\
           !x:real.
             x < b /\ abs (x - b) < d
             ==> M <= f x in
   let putnam_2024_b6_solution = --(&1 / &2) in
   !series_value:real->real->real. !c:real.
     (!a x:real.
        &0 <= x /\ x < &1
        ==>
        (\n:num.
           rpow (&(n + 1)) a *
           exp (&2 * &(n + 1)) *
           x pow ((n + 1) EXP 2))
        sums (series_value a x))
     ==>
     (((!a:real.
          a < c
          ==> tends_at_left
                (\x:real.
                   series_value a x * exp (--(&1 / (&1 - x))))
                (&1)
                (&0)) /\
       (!a:real.
          c < a
          ==> tends_at_left_posinfinity
                (\x:real.
                   series_value a x * exp (--(&1 / (&1 - x))))
                (&1)))
      <=>
      c = putnam_2024_b6_solution)`;;
