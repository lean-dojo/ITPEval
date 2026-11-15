(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a6
  (putnambench__hol-light__putnam_2024_a6): the determinant of the Hankel
  matrix formed from coefficients of a specified real power series near zero.
  This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

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
   !c:num->real. !n:num.
     (?e:real.
        &0 < e /\
        !x:real.
          abs x < e
          ==> (\k:num. c k * x pow k) sums
              ((&1 - &3 * x -
                sqrt (&1 - &14 * x + &9 * x pow 2)) / &4)) /\
     0 < n
     ==>
     ndet (\i j:num. c (i + j + 1)) n =
     (&10:real) pow ((n * (n - 1)) DIV 2)`;;
