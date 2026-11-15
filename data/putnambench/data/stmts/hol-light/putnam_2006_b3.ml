(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_b3:
  the maximum number of unordered bipartitions of an n-point planar set
  separated by a line is n choose 2 plus one. This file contains no proof.
*)

let binomial_output = open_out "/dev/null";;
let binomial_formatter = Format.formatter_of_out_channel binomial_output;;
let binomial_loaded =
  Toploop.use_file binomial_formatter "Library/binomial.ml";;
Format.pp_print_flush binomial_formatter ();;
close_out binomial_output;;
if not binomial_loaded then failwith "failed to load Library/binomial.ml";;

let statement =
  `let is_linear_partition =
     \(S:(real#real)->bool)
      (AB:((real#real)->bool)->bool).
       AB HAS_SIZE 2 /\
       ?A B:(real#real)->bool.
         A IN AB /\
         B IN AB /\
         ~(A = B) /\
         A UNION B = S /\
         A INTER B = {} /\
         ?m b:real.
           (!p:real#real.
              p IN A ==> m * FST p + b < SND p) /\
           (!p:real#real.
              p IN B ==> SND p < m * FST p + b) in
   let partition_count =
     \S:(real#real)->bool.
       CARD
         {AB:((real#real)->bool)->bool |
            is_linear_partition S AB} in
   let is_greatest =
     \(values:num->bool) (value:num).
       value IN values /\
       (!k:num. k IN values ==> k <= value) in
   !n:num.
     0 < n
     ==>
     is_greatest
       {k:num |
          ?S:(real#real)->bool.
            S HAS_SIZE n /\ partition_count S = k}
       (binom (n,2) + 1)`;;
