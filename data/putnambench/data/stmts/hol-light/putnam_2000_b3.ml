(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_b3:
  monotonicity and convergence to twice the highest frequency of the total
  zero multiplicities of successive derivatives of a finite sine polynomial.
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
  `let deriv =
     \(g:real->real) (x:real). @d:real. (g diffl d) x in
   let iterated_deriv =
     \(n:num) (g:real->real).
       (@D:num->real->real.
          D 0 = g /\
          (!k:num. D (SUC k) = deriv (D k))) n in
   !N:num.
   !a:num->real.
   !f:real->real.
   !mult:(real->real)->real->num.
   !M:num->num.
     0 < N /\
     ~(a N = &0) /\
     (!t:real.
        f t =
        sum (1..N) (\j:num. a j * sin (&2 * pi * &j * t))) /\
     (!g:real->real. !t:real.
        (?c:num. ~(iterated_deriv c g t = &0))
        ==> ~(iterated_deriv (mult g t) g t = &0) /\
            (!k:num.
               k < mult g t
               ==> iterated_deriv k g t = &0)) /\
     (!k:num.
        M k =
        nsum {t:real | &0 <= t /\ t < &1}
          (\t:real. mult (iterated_deriv k f) t))
     ==> (!i j:num. i <= j ==> M i <= M j) /\
         (?K:num. !k:num. K <= k ==> M k = 2 * N)`;;
