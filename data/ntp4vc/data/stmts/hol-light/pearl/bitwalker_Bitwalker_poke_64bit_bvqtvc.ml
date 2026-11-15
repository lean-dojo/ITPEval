(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_poke_64bit_bvqtvc: a fixed-width bit-vector
  verification condition for setting or clearing one selected bit of a
  64-bit value while preserving every other bit, together with the equivalent
  bounded-integer indexing formulation. This file contains no proof.
*)

needs "Library/words.ml";;

let bitwalker_nat_of_int = new_definition
  `bitwalker_nat_of_int (z:int) =
     if (&0:int) <= z then num_of_int z else 0`;;

let statement =
  `!left1:int32. !flag:bool. !value:int64.
     let u32 = \x:int32. (&(val x):int) in
     u32 left1 < (&64:int)
     ==>
     (u32 left1 <= (&63:int) \/
      word_ule left1 (word 63:int32)) /\
     (let o1:int32 = word_sub (word 63:int32) left1 in
      u32 o1 = (&63:int) - u32 left1
      ==>
      (let mask:int64 =
         word_shl (word 1:int64) (val (word_zx o1:int64)) in
       (if flag then T else T) /\
       (!result:int64.
          (if flag
           then result = word_or value mask
           else result = word_and value (word_not mask))
          ==>
          (!i:int32.
             ~(i = word_sub (word 63:int32) left1)
             ==>
             bit (val (word_zx i:int64)) result =
             bit (val (word_zx i:int64)) value) /\
          flag =
          bit
            (val
              (word_zx
                (word_sub (word 63:int32) left1):int64))
            result))) /\
     (!result:int64.
        ((!i:int32.
            ~(i = word_sub (word 63:int32) left1)
            ==>
            bit (val (word_zx i:int64)) result =
            bit (val (word_zx i:int64)) value) /\
         flag =
         bit
           (val
             (word_zx
               (word_sub (word 63:int32) left1):int64))
           result)
        ==>
        (!i:int.
           (((&0:int) <= i /\ i < (&64:int)) /\
            ~(i = (&63:int) - u32 left1))
           ==>
           bit (bitwalker_nat_of_int i) result =
           bit (bitwalker_nat_of_int i) value) /\
        flag =
        bit
          (bitwalker_nat_of_int ((&63:int) - u32 left1))
          result)`;;
