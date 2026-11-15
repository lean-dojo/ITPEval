(*
  Statement-only formalization of PutnamBench artifact putnam_1967_a2:
  the recurrence and exponential generating function for the number of
  symmetric nonnegative-integer matrices whose column sums are one. This file
  contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file analysis_formatter path);;
let transc_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `!S:num->num.
     S 0 = 1 /\
     (!n:num.
        1 <= n
        ==> S n =
            CARD
              {A:num->num->num |
                 (!i j:num.
                    i < n /\ j < n
                    ==> A i j = A j i) /\
                 (!j:num.
                    j < n
                    ==> nsum (0..n-1) (\i. A i j) = 1) /\
                 (!i j:num.
                    n <= i \/ n <= j
                    ==> A i j = 0)})
     ==>
     (!n:num.
        1 <= n
        ==> S (n + 1) = S n + n * S (n - 1)) /\
     (!x:real.
        (\n:num. &(S n) * (x pow n / &(FACT n)))
        sums exp (x + x pow 2 / &2))`;;
