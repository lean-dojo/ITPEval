(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitcount_BitCounting32_countqtvc: a 32-bit verification condition for
  the successive mask, shift, and add stages of a population-count algorithm,
  concluding consistency with the number of set bits. This file contains no
  proof.
*)

needs "Library/words.ml";;

let statement =
  `!n:int32.
     let x1 =
       word_sub n
         (word_and (word_ushr n 1) (word 1431655765)) in
     let x2 =
       word_add
         (word_and x1 (word 858993459))
         (word_and (word_ushr x1 2) (word 858993459)) in
     let x3 =
       word_and
         (word_add x2 (word_ushr x2 4))
         (word 252645135) in
     let x4 =
       word_add x3 (word_ushr x3 8) in
     let x5 =
       word_add x4 (word_ushr x4 16) in
     x1 =
       word_sub n
         (word_and (word_ushr n 1) (word 1431655765)) /\
     x2 =
       word_add
         (word_and x1 (word 858993459))
         (word_and (word_ushr x1 2) (word 858993459)) /\
     x3 =
       word_and
         (word_add x2 (word_ushr x2 4))
         (word 252645135) /\
     x4 = word_add x3 (word_ushr x3 8) /\
     x5 = word_add x4 (word_ushr x4 16) /\
     (val (word_and x5 (word 63)) = word_popcount n
      ==> val (word_and x5 (word 63)) = word_popcount n)`;;
