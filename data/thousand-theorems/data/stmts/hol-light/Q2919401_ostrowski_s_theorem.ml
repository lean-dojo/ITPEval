(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2919401,
  "Ostrowski's theorem": every nontrivial real-valued absolute value on the
  rationals is equivalent either to the usual absolute value or uniquely to
  the p-adic absolute value for a prime p. This file contains no proof.
*)

let ostrowski_transc_output = open_out "/dev/null";;
let ostrowski_transc_formatter =
  Format.formatter_of_out_channel ostrowski_transc_output;;
let ostrowski_previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file ostrowski_transc_formatter path);;
let ostrowski_transc_loaded =
  Toploop.use_file ostrowski_transc_formatter "Library/transc.ml";;
Hol_loader.file_loader := ostrowski_previous_file_loader;;
Format.pp_print_flush ostrowski_transc_formatter ();;
close_out ostrowski_transc_output;;
if not ostrowski_transc_loaded then
  failwith "failed to load Library/transc.ml";;

let Q2919401_OSTROWSKIS_THEOREM =
  `let is_rational =
     \x:real.
       ?m n:num. ~(n = 0) /\ abs x = &m / &n in
   let real_rpow =
     \x c:real.
       if x = &0 then &0 else exp (c * ln x) in
   let padic_absolute_value =
     \p:num. \x:real.
       if x = &0 then &0
       else
         @v:real.
           ?m n i j:num.
             ~(m = 0) /\ ~(n = 0) /\
             abs x = &m / &n /\
             (p EXP i) divides m /\
             ~((p EXP (SUC i)) divides m) /\
             (p EXP j) divides n /\
             ~((p EXP (SUC j)) divides n) /\
             v = (&p pow j) / (&p pow i) in
   let is_absolute_value =
     \f:real->real.
       (!x:real. is_rational x ==> &0 <= f x) /\
       (!x:real. is_rational x ==> (f x = &0 <=> x = &0)) /\
       (!x y:real.
          is_rational x /\ is_rational y
          ==> f (x * y) = f x * f y) /\
       (!x y:real.
          is_rational x /\ is_rational y
          ==> f (x + y) <= f x + f y) in
   let is_nontrivial =
     \f:real->real.
       ?x:real. is_rational x /\ ~(x = &0) /\ ~(f x = &1) in
   let is_equivalent =
     \f g:real->real.
       ?c:real.
         &0 < c /\
         !x:real. is_rational x ==> real_rpow (f x) c = g x in
   !f:real->real.
     is_absolute_value f /\ is_nontrivial f
     ==> is_equivalent f abs \/
         ?!p:num.
           prime p /\ is_equivalent f (padic_absolute_value p)`;;
