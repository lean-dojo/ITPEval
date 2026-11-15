(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/isqrt_von_neumann_VonNeumann32_isqrt32qtvc: the unsigned 32-bit
  von Neumann integer-square-root verification condition, including its
  initialization, loop preservation branches, and terminal bounds. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory wordsTheory;

val isqrt_von_neumann_VonNeumann32_isqrt32qtvc_statement =
  ``let sqr =
      \x : word32. x * x
    in
    let scale =
      \m : word32. (1w : word32) << w2n m
    in
    let half_scale =
      \m : word32.
        if m = (0w : word32) then
          (0w : word32)
        else
          (1w : word32) << w2n (m - (1w : word32))
    in
    let is_pow2 =
      \x : word32. \n : word32.
        (x && (scale n - (1w : word32))) = (0w : word32)
    in
      !x : word32.
        (16w : word32) <=+ (16w : word32) /\
        (32768w : word32) = half_scale (16w : word32) /\
        (1073741824w : word32) = sqr (32768w : word32) /\
        is_pow2 (0w : word32) (16w : word32) /\
        (0w : word32) <+ (65536w : word32) /\
        (0w : word32) =
          (0w : word32) * scale (16w : word32) /\
        x <=+ x /\
        x - x = sqr (0w : word32) /\
        (0w : word32) + scale (16w : word32) <=+
          (65536w : word32) /\
        x <=+
          sqr ((0w : word32) + scale (16w : word32)) -
            (1w : word32) /\
        !res_g m num : word32.
          m <=+ (16w : word32) /\
          is_pow2 res_g m /\
          res_g <+ (65536w : word32) /\
          num <=+ x /\
          x - num = sqr res_g /\
          res_g + scale m <=+ (65536w : word32) /\
          x <=+ sqr (res_g + scale m) - (1w : word32)
          ==>
          if ~(sqr (half_scale m) = (0w : word32)) then
            let b : word32 =
              (res_g * scale m) || sqr (half_scale m)
            in
              if b <=+ num then
                w2n (sqr (half_scale m) >>> 2) <
                  w2n (sqr (half_scale m)) /\
                m - (1w : word32) <=+ (16w : word32) /\
                half_scale m >>> 1 =
                  half_scale (m - (1w : word32)) /\
                sqr (half_scale m) >>> 2 =
                  sqr (half_scale m >>> 1) /\
                is_pow2
                  (res_g + half_scale m)
                  (m - (1w : word32)) /\
                res_g + half_scale m <+ (65536w : word32) /\
                ((res_g * scale m) >>> 1) || sqr (half_scale m) =
                  (res_g + half_scale m) *
                    scale (m - (1w : word32)) /\
                num - b <=+ x /\
                x - (num - b) = sqr (res_g + half_scale m) /\
                res_g + half_scale m +
                    scale (m - (1w : word32)) <=+
                  (65536w : word32) /\
                x <=+
                  sqr
                    (res_g + half_scale m +
                      scale (m - (1w : word32))) -
                    (1w : word32)
              else
                w2n (sqr (half_scale m) >>> 2) <
                  w2n (sqr (half_scale m)) /\
                m - (1w : word32) <=+ (16w : word32) /\
                half_scale m >>> 1 =
                  half_scale (m - (1w : word32)) /\
                sqr (half_scale m) >>> 2 =
                  sqr (half_scale m >>> 1) /\
                is_pow2 res_g (m - (1w : word32)) /\
                res_g <+ (65536w : word32) /\
                (res_g * scale m) >>> 1 =
                  res_g * scale (m - (1w : word32)) /\
                num <=+ x /\
                x - num = sqr res_g /\
                res_g + scale (m - (1w : word32)) <=+
                  (65536w : word32) /\
                x <=+
                  sqr
                    (res_g + scale (m - (1w : word32))) -
                    (1w : word32)
          else
            sqr (res_g * scale m) <=+ x /\
            x <=+
              sqr (res_g * scale m + (1w : word32)) -
                (1w : word32)``;
