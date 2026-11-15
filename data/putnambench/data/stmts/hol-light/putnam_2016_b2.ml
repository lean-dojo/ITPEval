(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_b2:
  the positive constants governing the asymptotic count of positive squarish
  integers are alpha = 3/4 and beta = 4/3, or no such constants exist. This
  file contains no proof.
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
  `let distance =
     \m n:num. if m <= n then n - m else m - n in
   let is_square =
     \n:num. ?k:num. n = k EXP 2 in
   let squarish =
     \n:num.
       is_square n \/
       (?w:num.
          is_square (distance n (w EXP 2)) /\
          (!v:num.
             distance n (w EXP 2) <= distance n (v EXP 2))) in
   let S =
     \N:num. CARD {n:num | n IN 1..N /\ squarish n} in
   let rpow =
     \x a:real. if x = &0 then &0 else exp (a * ln x) in
   let admissible =
     \alpha beta:real.
       &0 < alpha /\
       &0 < beta /\
       (\N:num. &(S N) / rpow (&N) alpha) tends_num_real beta in
   (!alpha beta:real.
      admissible alpha beta <=>
      (alpha,beta) = (&3 / &4,&4 / &3)) \/
   ~(?alpha beta:real. admissible alpha beta)`;;
