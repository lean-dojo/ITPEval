(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitcount_Hamming_hammingDqtvc: a 32-bit verification condition stating
  that the population count of a bitwise XOR equals the Hamming distance,
  counted as the positions where the input words differ. This file contains
  no proof.
*)

let bitcount_output = open_out "/dev/null";;
let bitcount_formatter = Format.formatter_of_out_channel bitcount_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file bitcount_formatter path);;
let words_loaded =
  Toploop.use_file bitcount_formatter "Library/words.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush bitcount_formatter ();;
close_out bitcount_output;;
if not words_loaded then failwith "failed to load Library/words.ml";;

let hammingD_logic = new_definition
  `hammingD_logic (a:(32)word) (b:(32)word) =
     CARD {i:num | i < 32 /\ ~(bit i a <=> bit i b)}`;;

let statement =
  `!result:(32)word. !a:(32)word. !b:(32)word.
     val result = word_popcount (word_xor a b)
     ==> val result = hammingD_logic a b`;;
