(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/isqrt_von_neumann_VonNeumann32_isqrt32qtvc: the 32-bit unsigned
  bit-vector verification condition for the von Neumann integer-square-root
  loop, including initialization, invariant preservation, and the terminal
  square bounds. This file contains no proof.
*)

needs "Library/words.ml";;

let statement =
  `let zero32:int32 = word 0 in
   let one32:int32 = word 1 in
   let two32:int32 = word 2 in
   let sixteen32:int32 = word 16 in
   let bound32:int32 = word 65536 in
   let shl1 = \n:int32. word_shl one32 (val n) in
   let sqr = \z:int32. word_mul z z in
   let half_power =
     \n:int32.
       if n = zero32 then zero32 else shl1 (word_sub n one32) in
   let is_pow2 =
     \z:int32. \n:int32.
       word_and z (word_sub (shl1 n) one32) = zero32 in
   !x:int32.
     word_ule sixteen32 sixteen32 /\
     (word 32768:int32) = half_power sixteen32 /\
     (word 1073741824:int32) = sqr (word 32768:int32) /\
     is_pow2 zero32 sixteen32 /\
     word_ult zero32 bound32 /\
     zero32 = word_mul zero32 (shl1 sixteen32) /\
     word_ule x x /\
     word_sub x x = sqr zero32 /\
     word_ule (word_add zero32 (shl1 sixteen32)) bound32 /\
     word_ule x
       (word_sub (sqr (word_add zero32 (shl1 sixteen32))) one32) /\
     (!res_g:int32. !m:int32. !num:int32.
        word_ule m sixteen32 /\
        is_pow2 res_g m /\
        word_ult res_g bound32 /\
        word_ule num x /\
        word_sub x num = sqr res_g /\
        word_ule (word_add res_g (shl1 m)) bound32 /\
        word_ule x (word_sub (sqr (word_add res_g (shl1 m))) one32)
        ==>
        (let m1 = word_sub m one32 in
         let p = half_power m in
         if ~(sqr p = zero32) then
           let b =
             word_or (word_mul res_g (shl1 m)) (sqr p) in
           if word_ule b num then
             val (word_ushr (sqr p) (val two32)) < val (sqr p) /\
             word_ule m1 sixteen32 /\
             word_ushr p (val one32) = half_power m1 /\
             word_ushr (sqr p) (val two32) =
               sqr (word_ushr p (val one32)) /\
             is_pow2 (word_add res_g p) m1 /\
             word_ult (word_add res_g p) bound32 /\
             word_or
               (word_ushr (word_mul res_g (shl1 m)) (val one32))
               (sqr p) =
               word_mul (word_add res_g p) (shl1 m1) /\
             word_ule (word_sub num b) x /\
             word_sub x (word_sub num b) =
               sqr (word_add res_g p) /\
             word_ule
               (word_add (word_add res_g p) (shl1 m1))
               bound32 /\
             word_ule x
               (word_sub
                 (sqr (word_add (word_add res_g p) (shl1 m1)))
                 one32)
           else
             val (word_ushr (sqr p) (val two32)) < val (sqr p) /\
             word_ule m1 sixteen32 /\
             word_ushr p (val one32) = half_power m1 /\
             word_ushr (sqr p) (val two32) =
               sqr (word_ushr p (val one32)) /\
             is_pow2 res_g m1 /\
             word_ult res_g bound32 /\
             word_ushr (word_mul res_g (shl1 m)) (val one32) =
               word_mul res_g (shl1 m1) /\
             word_ule num x /\
             word_sub x num = sqr res_g /\
             word_ule (word_add res_g (shl1 m1)) bound32 /\
             word_ule x
               (word_sub (sqr (word_add res_g (shl1 m1))) one32)
         else
           word_ule (sqr (word_mul res_g (shl1 m))) x /\
           word_ule x
             (word_sub
               (sqr (word_add (word_mul res_g (shl1 m)) one32))
               one32)))`;;
