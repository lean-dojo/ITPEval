(*
  Statement-only formalization of Thousand Theorems corpus artifact Q718875,
  "Erdős–Ko–Rado theorem": an intersecting family of r-element subsets of
  Fin n, with r at most n / 2, has at most (n - 1) choose (r - 1) members.
  This file contains no proof.
*)

let erdos_ko_rado_binomial_output = open_out "/dev/null";;
let erdos_ko_rado_binomial_formatter =
  Format.formatter_of_out_channel erdos_ko_rado_binomial_output;;
let erdos_ko_rado_binomial_loaded =
  Toploop.use_file erdos_ko_rado_binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush erdos_ko_rado_binomial_formatter ();;
close_out erdos_ko_rado_binomial_output;;
if not erdos_ko_rado_binomial_loaded then
  failwith "failed to load Library/binomial.ml";;

let Q718875_ERDOS_KO_RADO_THEOREM =
  `!n r:num. !family:(num->bool)->bool.
     FINITE family /\
     (!s:num->bool.
        s IN family
        ==> FINITE s /\ s SUBSET {i:num | i < n} /\ CARD s = r) /\
     (!s t:num->bool.
        s IN family /\ t IN family ==> ~DISJOINT s t) /\
     r <= n DIV 2
     ==> CARD family <= binom (n - 1,r - 1)`;;
