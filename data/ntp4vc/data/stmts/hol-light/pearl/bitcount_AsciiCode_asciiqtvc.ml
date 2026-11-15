(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitcount_AsciiCode_asciiqtvc: a 32-bit verification condition in
  which the population-count parity is placed in the top bit, preserving the
  lower 31 bits and yielding an even-parity word. This file contains no proof.
*)

needs "Library/words.ml";;

let statement =
  `!b c:int32.
     ~bit (val (word_sub (word 32:int32) (word 1))) b
     ==> val c = word_popcount b
     ==> (word_ult (word 31:int32) (word 32) \/ 31 < 32) /\
         (let maskbit:int32 =
            word_shl c (val (word 31:int32)) in
          maskbit = word_shl c 31
          ==>
          let code:int32 = word_or b maskbit in
          (word_subword code (0,31):31 word) =
          (word_subword b (0,31):31 word) /\
          word_evenparity code)`;;
