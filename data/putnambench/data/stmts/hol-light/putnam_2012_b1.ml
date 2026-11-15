(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_b1:
  closure under pointwise multiplication for a class of functions from the
  nonnegative reals to themselves containing exp(x) - 1 and ln(x + 1), and
  closed under addition, composition, and nonnegative subtraction. This file
  contains no proof.
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
  `let nonnegative_function =
     \f:real->real.
       (!x:real. &0 <= x ==> &0 <= f x) /\
       (!x:real. x < &0 ==> f x = &0) in
   let f1 =
     \x:real. if &0 <= x then exp x - &1 else &0 in
   let f2 =
     \x:real. if &0 <= x then ln (x + &1) else &0 in
   let add =
     \(f:real->real) (g:real->real) (x:real).
       if &0 <= x then f x + g x else &0 in
   let compose =
     \(f:real->real) (g:real->real) (x:real).
       if &0 <= x then f (g x) else &0 in
   let subtract =
     \(f:real->real) (g:real->real) (x:real).
       if &0 <= x then f x - g x else &0 in
   let multiply =
     \(f:real->real) (g:real->real) (x:real).
       if &0 <= x then f x * g x else &0 in
   !S:(real->real)->bool.
     (!f:real->real. S f ==> nonnegative_function f) /\
     S f1 /\
     S f2 /\
     (!f g:real->real. S f /\ S g ==> S (add f g)) /\
     (!f g:real->real. S f /\ S g ==> S (compose f g)) /\
     (!f g:real->real.
        S f /\ S g /\
        (!x:real. &0 <= x ==> g x <= f x)
        ==> S (subtract f g))
     ==>
     !f g:real->real. S f /\ S g ==> S (multiply f g)`;;
