(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_b3:
  evaluation of a two-variable limit involving a double power series over
  positive integer pairs whose ratio lies between one half and two. This file
  contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let A =
     \(xy:real#real).
       &0 <= FST xy /\ FST xy < &1 /\
       &0 <= SND xy /\ SND xy < &1 in
   let S =
     \x y:real.
       suminf
         (\m:num.
            suminf
              (\n:num.
                 if 0 < m /\ 0 < n /\
                    &1 / &2 <= &m / &n /\ &m / &n <= &2
                 then x pow m * y pow n
                 else &0)) in
   let tends_within_A =
     \(f:real#real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !xy:real#real.
                 A xy /\
                 &0 <
                   max (abs (FST xy - &1)) (abs (SND xy - &1)) /\
                 max (abs (FST xy - &1)) (abs (SND xy - &1)) < d
                 ==> abs (f xy - l) < e in
   let putnam_1999_b3_solution = &3 in
   tends_within_A
     (\xy:real#real.
        (&1 - FST xy * (SND xy) pow 2) *
        (&1 - (FST xy) pow 2 * SND xy) *
        S (FST xy) (SND xy))
     putnam_1999_b3_solution`;;
