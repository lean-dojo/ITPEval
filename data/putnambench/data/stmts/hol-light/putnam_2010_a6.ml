(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_a6:
  divergence of an improper integral associated with a strictly decreasing
  continuous function on the nonnegative reals that tends to zero. This file
  contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/transc.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let continuous_on_nonnegative =
     \(f:real->real).
       !x:real.
         &0 <= x
         ==> !e:real.
               &0 < e
               ==> ?d:real.
                     &0 < d /\
                     !y:real.
                       &0 <= y /\ abs (y - x) < d
                       ==> abs (f y - f x) < e in
   let tends_at_posinfinity =
     \(g:real->real) (l:real).
       !e:real.
         &0 < e
         ==> ?B:real.
               !x:real. B <= x ==> abs (g x - l) < e in
   !f:real->real.
     (!x y:real.
        &0 <= x /\ &0 <= y /\ x < y
        ==> f y < f x) /\
     continuous_on_nonnegative f /\
     tends_at_posinfinity f (&0)
     ==>
     ~(?l:real.
         tends_at_posinfinity
           (\z:real.
              integral(&0,z)
                (\x:real. (f x - f (x + &1)) / f x))
           l)`;;
