(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_b4:
  the complex determinant of the tied-game and win-loss matrices for 2011
  multiplayer games is a nonnegative integer divisible by 2^2010. This file
  contains no proof.
*)

let permutations_output = open_out "/dev/null";;
let permutations_formatter =
  Format.formatter_of_out_channel permutations_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file permutations_formatter path);;
let permutations_loaded =
  Toploop.use_file permutations_formatter "Library/permutations.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush permutations_formatter ();;
close_out permutations_output;;
if not permutations_loaded then
  failwith "failed to load Library/permutations.ml";;

let statement =
  `let cadd =
     \(z:real#real) w.
       (FST z + FST w,SND z + SND w) in
   let cmul =
     \(z:real#real) w.
       (FST z * FST w - SND z * SND w,
        FST z * SND w + SND z * FST w) in
   let csum =
     \s f. iterate cadd s f in
   let cproduct =
     \s f. iterate cmul s f in
   let complex_det =
     \A:2011->2011->real#real.
       csum {p:2011->2011 | p permutes (UNIV:2011->bool)}
         (\p. cmul (sign p,&0)
              (cproduct (UNIV:2011->bool) (\i. A i (p i)))) in
   !games:2011->2011->bool.
     let T =
       \h k.
         (&(CARD {g:2011 | games g h = games g k}),&0) in
     let W =
       \h k.
         (&(CARD {g:2011 | games g h /\ ~(games g k)}) -
          &(CARD {g:2011 | ~(games g h) /\ games g k}),&0) in
     ?n:num.
       complex_det (\h k. cadd (T h k) (cmul (&0,&1) (W h k))) =
       (&n,&0) /\
       2 EXP 2010 divides n`;;
