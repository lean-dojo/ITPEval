(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/base_info_BaseInfo_wmpn_limb_size_in_base_2qtvc:
  the verification condition deriving the bit length of a positive 64-bit
  limb from a signed 32-bit leading-zero count, via the complementary shift
  and enclosing powers of two. This file contains no proof.
*)

let limb_size_output = open_out "/dev/null";;
let limb_size_formatter =
  Format.formatter_of_out_channel limb_size_output;;
let limb_size_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file limb_size_formatter path);;
let limb_size_words_loaded =
  Toploop.use_file limb_size_formatter "Library/words.ml";;
Hol_loader.file_loader := limb_size_previous_loader;;
Format.pp_print_flush limb_size_formatter ();;
close_out limb_size_output;;
if not limb_size_words_loaded then
  failwith "failed to load Library/words.ml";;

let statement =
  `let uint64_in_bounds =
     \z:int.
       (&0:int) <= z /\ z <= (&18446744073709551615:int) in
   !u:int64.
     (&0:int) < (&(val u):int)
     ==>
     (&0:int) < (&(val u):int) /\
     (!o1:int32.
        ((&2:int) pow (num_of_int (ival o1))) * (&(val u):int) <=
          (&18446744073709551615:int) /\
        (&18446744073709551615:int) <
          (&2:int) * ((&2:int) pow (num_of_int (ival o1))) *
          (&(val u):int) /\
        (&0:int) <= ival o1 /\
        ival o1 < (&64:int)
        ==>
        (&0:int) <= ival o1 /\
        (!shift:int64.
           (&(val shift):int) = ival o1
           ==>
           uint64_in_bounds
             ((&64:int) - (&(val shift):int)) /\
           (!r:int64.
              (&(val r):int) =
                (&64:int) - (&(val shift):int)
              ==>
              ((&1:int) <= (&(val r):int) /\
               (&(val r):int) <= (&64:int)) /\
              ((&2:int) pow
                 (num_of_int ((&(val r):int) - (&1:int)))) <=
                (&(val u):int) /\
              (&(val u):int) <
                ((&2:int) pow (num_of_int (&(val r):int))))))`;;
