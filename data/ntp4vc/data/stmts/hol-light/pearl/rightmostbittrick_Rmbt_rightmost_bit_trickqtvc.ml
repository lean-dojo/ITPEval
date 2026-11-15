(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/rightmostbittrick_Rmbt_rightmost_bit_trickqtvc: a 64-bit verification
  condition stating that a nonzero word AND its two's-complement negation
  isolates its rightmost set bit. This file contains no proof.
*)

let rmbt_output = open_out "/dev/null";;
let rmbt_formatter = Format.formatter_of_out_channel rmbt_output;;
let rmbt_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file rmbt_formatter path);;
let rmbt_words_loaded =
  Toploop.use_file rmbt_formatter "Library/words.ml";;
Hol_loader.file_loader := rmbt_previous_loader;;
Format.pp_print_flush rmbt_formatter ();;
close_out rmbt_output;;
if not rmbt_words_loaded then failwith "failed to load Library/words.ml";;

let rmbt_nth = new_definition
  `rmbt_nth (w:int64) (j:int) =
     if (&0:int) <= j then bit (num_of_int j) w else F`;;

let rmbt_eq_sub = new_definition
  `rmbt_eq_sub (a:int64) (b:int64) (i:int) (n:int) =
     (!j:int.
        i <= j /\ j < i + n
        ==> (rmbt_nth a j <=> rmbt_nth b j))`;;

let rmbt_eq_sub_bv = new_definition
  `rmbt_eq_sub_bv (a:int64) (b:int64) (i:int64) (n:int64) =
     rmbt_eq_sub a b (&(val i):int) (&(val n):int)`;;

let statement =
  `!x:int64.
     ~(x = (word 0:int64))
     ==>
     ~(x = (word 0:int64)) /\
     (!p_bv:int64.
        word_ult p_bv (word 64:int64) /\
        rmbt_eq_sub_bv
          x (word 0:int64) (word 0:int64) p_bv /\
        bit (val p_bv) x
        ==>
        let r:int64 = word_and x (word_neg x) in
        ((&0:int) <= (&(val p_bv):int) /\
         (&(val p_bv):int) < (&64:int)) /\
        rmbt_eq_sub
          x (word 0:int64) (&0:int) (&(val p_bv):int) /\
        rmbt_nth x (&(val p_bv):int) /\
        rmbt_eq_sub
          r (word 0:int64) (&0:int) (&(val p_bv):int) /\
        rmbt_eq_sub
          r (word 0:int64)
          ((&(val p_bv):int) + (&1:int))
          ((&63:int) - (&(val p_bv):int)) /\
        rmbt_nth r (&(val p_bv):int))`;;
