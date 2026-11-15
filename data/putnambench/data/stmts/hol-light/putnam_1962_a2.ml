(*
  Statement-only formalization of PutnamBench artifact putnam_1962_a2:
  classification of nonnegative real functions whose interval average equals
  the geometric mean of their endpoint values. The answer is the published
  rational-square family. This file contains no proof.
*)

let analysis_output = open_out "/dev/null";;
let analysis_formatter = Format.formatter_of_out_channel analysis_output;;
let analysis_loaded =
  Toploop.use_file analysis_formatter "Library/analysis.ml";;
Format.pp_print_flush analysis_formatter ();;
close_out analysis_output;;
if not analysis_loaded then failwith "failed to load Library/analysis.ml";;

let statement =
  `let interval_integral =
     \(f:real->real) (x:real).
       if integrable(&0,x) f
       then integral(&0,x) f
       else &0 in
   let solution =
     \g:real->real.
       (?a c:real.
          &0 <= a /\
          (!x. g x = a / (&1 - c * x) pow 2)) in
   let condition =
     \(s:real->bool) (f:real->real).
       (!x. &0 <= f x) /\
       (!x. x IN s
            ==> interval_integral f x / x =
                sqrt (f (&0) * f x)) in
   !P:(real->bool)->(real->real)->bool.
     (!s f. P s f <=> condition s f)
     ==>
     ((!f.
         (P {x | &0 < x} f
          ==> ?g. solution g /\
                  (!x. &0 <= x ==> f x = g x)) /\
         (!e. &0 < e
              ==> P {x | &0 < x /\ x < e} f
                  ==> ?g. solution g /\
                          (!x. &0 <= x /\ x < e ==> f x = g x))) /\
      (!f. solution f
           ==> P {x | &0 < x} f \/
               (?e. &0 < e /\ P {x | &0 < x /\ x < e} f)))`;;
