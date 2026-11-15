(*
  Statement-only formalization of PutnamBench artifact putnam_1964_a3:
  the sum of the cubic products of the two new interval lengths formed by an
  injective dense sequence in (0,1) is 1/3. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let earlier_left =
     \(x:num->real) (n:num) (p:real).
       p = &0 \/ ?i:num. i < n /\ p = x i /\ p < x n in
   let earlier_right =
     \(x:num->real) (n:num) (p:real).
       p = &1 \/ ?i:num. i < n /\ p = x i /\ x n < p in
   let left_endpoint =
     \(x:num->real) (n:num).
       @p:real.
         earlier_left x n p /\
         (!q:real. earlier_left x n q ==> q <= p) in
   let right_endpoint =
     \(x:num->real) (n:num).
       @p:real.
         earlier_right x n p /\
         (!q:real. earlier_right x n q ==> p <= q) in
   !x a b:num->real.
     (!n:num. &0 < x n /\ x n < &1) /\
     (!m n:num. x m = x n ==> m = n) /\
     (!y:real.
        &0 < y /\ y < &1
        ==> !e:real. &0 < e ==> ?n:num. abs (x n - y) < e) /\
     a = (\n:num. x n - left_endpoint x n) /\
     b = (\n:num. right_endpoint x n - x n)
     ==> (\n:num. a n * b n * (a n + b n)) sums (&1 / &3)`;;
