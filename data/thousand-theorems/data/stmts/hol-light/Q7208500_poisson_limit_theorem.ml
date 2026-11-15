(*
  Statement-only formalization of Thousand Theorems corpus artifact Q7208500,
  "Poisson limit theorem": for a fixed natural number k and any real sequence
  p, if n * p(n) tends to r, then the corresponding binomial probability term
  tends to exp(-r) * r^k / k!. This file contains no proof.
*)

let q7208500_output = open_out "/dev/null";;
let q7208500_formatter = Format.formatter_of_out_channel q7208500_output;;
let q7208500_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q7208500_formatter path);;
let q7208500_binomial_loaded =
  Toploop.use_file q7208500_formatter "Library/binomial.ml";;
let q7208500_transc_loaded =
  Toploop.use_file q7208500_formatter "Library/transc.ml";;
Hol_loader.file_loader := q7208500_previous_loader;;
Format.pp_print_flush q7208500_formatter ();;
close_out q7208500_output;;
if not q7208500_binomial_loaded then
  failwith "Q7208500: failed to load Library/binomial.ml";;
if not q7208500_transc_loaded then
  failwith "Q7208500: failed to load Library/transc.ml";;

let Q7208500_POISSON_LIMIT_THEOREM =
  `let seq_tends = \a:num->real. \l:real.
     !epsilon:real.
       &0 < epsilon
       ==> ?N:num. !n:num.
             N <= n ==> abs(a n - l) < epsilon in
   !k:num. !p:num->real. !r:real.
     seq_tends (\n:num. &n * p n) r
     ==>
     seq_tends
       (\n:num.
          &(binom(n,k)) * (p n) pow k *
          (&1 - p n) pow (n - k))
       (exp(--r) * r pow k / &(FACT k))`;;
