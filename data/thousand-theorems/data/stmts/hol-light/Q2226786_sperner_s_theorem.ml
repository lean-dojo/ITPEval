(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2226786,
  "Sperner's theorem": the cardinality of a finite inclusion-antichain of
  subsets of a finite carrier is at most the middle binomial coefficient.
  This file contains no proof.
*)

let sperner_binomial_output = open_out "/dev/null";;
let sperner_binomial_formatter =
  Format.formatter_of_out_channel sperner_binomial_output;;
let sperner_binomial_loaded =
  Toploop.use_file sperner_binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush sperner_binomial_formatter ();;
close_out sperner_binomial_output;;
if not sperner_binomial_loaded then
  failwith "failed to load Library/binomial.ml";;

let Q2226786_SPERNER_THEOREM =
  `!V:A->bool. !family:(A->bool)->bool.
     FINITE V /\
     FINITE family /\
     (!s. s IN family ==> s SUBSET V) /\
     (!s t. s IN family /\ t IN family /\ s SUBSET t ==> s = t)
     ==> CARD family <= binom (CARD V,CARD V DIV 2)`;;
