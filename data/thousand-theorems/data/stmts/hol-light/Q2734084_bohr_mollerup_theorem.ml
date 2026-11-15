(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2734084
  (thousand-theorems__hol-light__Q2734084), "Bohr–Mollerup theorem": every
  positive real-valued function on the positive reals whose logarithm is
  convex, which is normalized at one and satisfies the Gamma recurrence,
  agrees there with the real Gamma function, encoded by its Gauss limit.
  This file contains no proof.
*)

let bohr_mollerup_transc_output = open_out "/dev/null";;
let bohr_mollerup_transc_formatter =
  Format.formatter_of_out_channel bohr_mollerup_transc_output;;
let bohr_mollerup_previous_file_loader =
  !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file bohr_mollerup_transc_formatter path);;
let bohr_mollerup_transc_loaded =
  Toploop.use_file bohr_mollerup_transc_formatter "Library/transc.ml";;
Hol_loader.file_loader := bohr_mollerup_previous_file_loader;;
Format.pp_print_flush bohr_mollerup_transc_formatter ();;
close_out bohr_mollerup_transc_output;;
if not bohr_mollerup_transc_loaded then
  failwith "failed to load Library/transc.ml";;

let Q2734084_BOHR_MOLLERUP_THEOREM =
  `let real_gamma =
      \x:real.
        @g:real.
          !epsilon:real.
            &0 < epsilon
            ==> ?N:num.
                  !n:num.
                    N <= n
                    ==> abs
                          (exp(x * ln(&n)) * &(FACT n) /
                           product (0..n) (\m. x + &m) - g) < epsilon in
   let log_convex_on_positive =
      \f:real->real.
        !x y u v:real.
          &0 < x /\ &0 < y /\
          &0 <= u /\ &0 <= v /\ u + v = &1
          ==> ln(f(u * x + v * y)) <=
              u * ln(f x) + v * ln(f y) in
   !f:real->real.
     log_convex_on_positive f /\
     (!y. &0 < y ==> f(y + &1) = y * f y) /\
     (!y. &0 < y ==> &0 < f y) /\
     f(&1) = &1
     ==> !x. &0 < x ==> f x = real_gamma x`;;
