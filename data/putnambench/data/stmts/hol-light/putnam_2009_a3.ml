(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_a3:
  the determinants of the row-major n by n cosine matrices converge to zero
  as n tends to infinity. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let ndet =
     \(A:num->num->real) n.
       sum {p:num->num |
              BIJ p (0..n-1) (0..n-1) /\
              (!i:num. ~(i IN 0..n-1) ==> p i = i)}
           (\p.
              (if EVEN
                    (CARD
                      {(i,j) |
                         i < n /\ j < n /\ i < j /\ p j < p i})
               then &1
               else -- &1) *
              product (0..n-1) (\i. A i (p i))) in
   !cos_matrix:num->num->num->real.
     (!n i j:num.
        i < n /\ j < n
        ==> cos_matrix n i j = cos (&(1 + n * i + j)))
     ==>
     (\n:num. ndet (cos_matrix n) n) tends_num_real &0`;;
