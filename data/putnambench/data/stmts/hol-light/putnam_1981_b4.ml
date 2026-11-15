(*
  Statement-only formalization of PutnamBench artifact putnam_1981_b4:
  whether a real-linear set of five-by-seven real matrices containing ranks
  zero, one, two, four, and five must also contain rank three; the answer is
  false. This file contains no proof.
*)

let vectors_output = open_out "/dev/null";;
let vectors_formatter = Format.formatter_of_out_channel vectors_output;;
let vectors_loaded =
  Toploop.use_file vectors_formatter "Multivariate/vectors.ml";;
Format.pp_print_flush vectors_formatter ();;
close_out vectors_output;;
if not vectors_loaded then failwith "failed to load Multivariate/vectors.ml";;

let statement =
  `let VAB =
     \V:(real^7^5)->bool.
       !A B:real^7^5.
         A IN V /\ B IN V
         ==> !r s:real. r %% A + s %% B IN V in
   let Vrank =
     \V:(real^7^5)->bool. \k:num.
       ?A:real^7^5. A IN V /\ rank A = k in
   let putnam_1981_b4_solution = F in
   ((!V:(real^7^5)->bool.
       VAB V /\
       Vrank V 0 /\
       Vrank V 1 /\
       Vrank V 2 /\
       Vrank V 4 /\
       Vrank V 5
       ==> Vrank V 3) <=>
    putnam_1981_b4_solution)`;;
