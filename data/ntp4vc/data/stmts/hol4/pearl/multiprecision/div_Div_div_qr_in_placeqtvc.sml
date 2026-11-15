(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_div_qr_in_placeqtvc: the verification
  condition for in-place multiprecision quotient-and-remainder division,
  including the one-limb, two-limb, normalization, shifting, and
  quotient-padding branches. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val dqip_radix_def = Define `
  dqip_radix = (18446744073709551616 : int)`;

val dqip_half_radix_def = Define `
  dqip_half_radix = (9223372036854775808 : int)`;

val dqip_to_num_def = Define `
  dqip_to_num (z : int) = if z < (0 : int) then 0 else Num z`;

val dqip_int32_in_bounds_def = Define `
  dqip_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val dqip_uint_def = Define `
  dqip_uint (w : word64) = &(w2n w)`;

val dqip_power_def = Define `
  dqip_power (base : int) (exponent : int) =
    base ** dqip_to_num exponent`;

(* The observation tuple is exactly
   ((data length, total data map), offset, min, max, writable, zone). *)
val dqip_data_length_def = Define `
  dqip_data_length
      (obs :
        'p -> (num # (int -> word64)) #
          (int # (int # (int # (bool # 'z)))))
      (p : 'p) =
    FST (FST (obs p))`;

val dqip_offset_def = Define `
  dqip_offset obs (p : 'p) =
    FST (SND (obs p))`;

val dqip_minimum_def = Define `
  dqip_minimum obs (p : 'p) =
    FST (SND (SND (obs p)))`;

val dqip_maximum_def = Define `
  dqip_maximum obs (p : 'p) =
    FST (SND (SND (SND (obs p))))`;

val dqip_writable_def = Define `
  dqip_writable obs (p : 'p) =
    FST (SND (SND (SND (SND (obs p)))))`;

val dqip_zone_def = Define `
  dqip_zone obs (p : 'p) =
    SND (SND (SND (SND (SND (obs p)))))`;

val dqip_pelts_def = Define `
  dqip_pelts
      (obs :
        'p -> (num # (int -> word64)) #
          (int # (int # (int # (bool # 'z)))))
      (p : 'p)
      (index : int) =
    SND (FST (obs p)) index`;

val dqip_valid_def = Define `
  dqip_valid obs (p : 'p) (size : int) <=>
    dqip_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= dqip_minimum obs p /\
     dqip_minimum obs p <= dqip_offset obs p) /\
    dqip_offset obs p + size <= dqip_maximum obs p /\
    dqip_maximum obs p <= &(dqip_data_length obs p)`;

val dqip_same_shape_def = Define `
  dqip_same_shape obs (newer : 'p) (older : 'p) <=>
    dqip_data_length obs newer = dqip_data_length obs older /\
    dqip_offset obs newer = dqip_offset obs older /\
    dqip_minimum obs newer = dqip_minimum obs older /\
    dqip_maximum obs newer = dqip_maximum obs older /\
    dqip_writable obs newer = dqip_writable obs older /\
    dqip_zone obs newer = dqip_zone obs older`;

val dqip_access_at_def = Define `
  dqip_access_at obs (p : 'p) (index : int) <=>
    dqip_minimum obs p <= index /\ index < dqip_maximum obs p`;

val dqip_map_updated_at_def = Define `
  dqip_map_updated_at
      obs (newer : 'p) (older : 'p) (index : int) (limb : word64) <=>
    !query : int.
      dqip_pelts obs newer query =
        if query = index then limb else dqip_pelts obs older query`;

val dqip_updated_at_and_stored_def = Define `
  dqip_updated_at_and_stored
      obs (newer : 'p) (older : 'p) (index : int) (limb : word64) <=>
    dqip_map_updated_at obs newer older index limb /\
    dqip_pelts obs newer index = limb`;

val dqip_map_eq_sub_shift_def = Define `
  dqip_map_eq_sub_shift
      obs (first : 'p) (second : 'p)
      (first_offset : int) (second_offset : int) (size : int) <=>
    !i : int.
      (0 : int) <= i /\ i < size ==>
      dqip_pelts obs first (first_offset + i) =
        dqip_pelts obs second (second_offset + i)`;

val dqip_outside_unchanged_def = Define `
  dqip_outside_unchanged
      obs (current : 'p) (original : 'p) (size : int) <=>
    !j : int.
      j < dqip_offset obs current \/
      dqip_offset obs current + size <= j ==>
      dqip_pelts obs current j = dqip_pelts obs original j`;

val dqip_copied_range_def = Define `
  dqip_copied_range
      obs (current : 'p) (source : 'p) (original : 'p) (size : int) <=>
    dqip_map_eq_sub_shift
      obs current source
      (dqip_offset obs current) (dqip_offset obs source) size /\
    dqip_outside_unchanged obs current original size`;

val dqip_value_from_def = Define `
  (dqip_value_from obs (p : 'p) (index : int) 0 = (0 : int)) /\
  (dqip_value_from obs p index (SUC count) =
     dqip_uint (dqip_pelts obs p index) +
       dqip_radix *
         dqip_value_from obs p (index + (1 : int)) count)`;

val dqip_value_def = Define `
  dqip_value obs (p : 'p) (size : int) =
    dqip_value_from
      obs p (dqip_offset obs p) (dqip_to_num size)`;

val dqip_normalized_def = Define `
  dqip_normalized obs (p : 'p) (size : word32) <=>
    dqip_valid obs p (w2i size) /\
    dqip_half_radix <=
      dqip_uint
        (dqip_pelts obs p
          (dqip_offset obs p + w2i size - (1 : int)))`;

val dqip_word_flag_def = Define `
  dqip_word_flag (word : word32) (constant : word32) (flag : bool) <=>
    (w2i word = w2i constant ==> flag = T) /\
    (flag = T ==> word = constant)`;

val dqip_shift_count_bounds_def = Define `
  dqip_shift_count_bounds (count : word64) <=>
    (0 : int) < dqip_uint count /\ dqip_uint count < (64 : int)`;

val dqip_clz_conditions_def = Define `
  dqip_clz_conditions (most_significant : word64) (clz : word32) <=>
    dqip_power (2 : int) (w2i clz) * dqip_uint most_significant <
      dqip_radix /\
    dqip_radix <=
      (2 : int) * dqip_power (2 : int) (w2i clz) *
        dqip_uint most_significant /\
    ((0 : int) <= w2i clz /\ w2i clz < (64 : int)) /\
    dqip_power (2 : int) (w2i clz) * dqip_uint most_significant <=
      dqip_radix - dqip_power (2 : int) (w2i clz)`;

val dqip_qr_post_def = Define `
  dqip_qr_post
      obs (original_x : 'p) (quotient : 'p)
      (divisor : 'p) (remainder : 'p)
      (sx : word32) (sy : word32) <=>
    dqip_value obs original_x (w2i sx) =
      dqip_value obs quotient (w2i sx - w2i sy + (1 : int)) *
        dqip_value obs divisor (w2i sy) +
      dqip_value obs remainder (w2i sy) /\
    dqip_value obs remainder (w2i sy) <
      dqip_value obs divisor (w2i sy)`;

val dqip_division_premise_def = Define `
  dqip_division_premise
      obs (dividend : 'p) (quotient : 'p)
      (divisor : 'p) (remainder : 'p)
      (total_size : int) (divisor_size : int) (qh : word64) <=>
    dqip_value obs dividend total_size =
      (dqip_value obs quotient (total_size - divisor_size) +
       dqip_power dqip_radix (total_size - divisor_size) * dqip_uint qh) *
        dqip_value obs divisor divisor_size +
      dqip_value obs remainder divisor_size /\
    dqip_value obs remainder divisor_size <
      dqip_value obs divisor divisor_size /\
    (0 : int) <= dqip_uint qh /\ dqip_uint qh <= (1 : int)`;

val dqip_quotient_padding_def = Define `
  dqip_quotient_padding
      obs (quotient : 'p)
      (sx : word32) (sy : word32) (adjust : word32) <=>
    !flag : bool.
      dqip_word_flag adjust (0w : word32) flag ==>
      if flag = T then
        dqip_int32_in_bounds (w2i sx - w2i sy) /\
        (!index : word32.
           w2i index = w2i sx - w2i sy ==>
           (dqip_access_at
              obs quotient (dqip_offset obs quotient + w2i index) /\
            dqip_writable obs quotient = T) /\
           (!padded : 'p.
              dqip_same_shape obs padded quotient ==>
              dqip_updated_at_and_stored
                obs padded quotient
                (dqip_offset obs padded + w2i index) (0w : word64) ==>
              dqip_value obs padded (w2i sx - w2i sy + (1 : int)) =
                dqip_value obs quotient
                  (w2i sx - w2i sy + w2i adjust)))
      else
        dqip_value obs quotient (w2i sx - w2i sy + (1 : int)) =
          dqip_value obs quotient (w2i sx - w2i sy + w2i adjust)`;

val dqip_finish_with_padding_def = Define `
  dqip_finish_with_padding
      obs (original_x : 'p) (quotient : 'p)
      (divisor : 'p) (remainder : 'p)
      (sx : word32) (sy : word32) (adjust : word32) <=>
    dqip_quotient_padding obs quotient sx sy adjust /\
    (!padded : 'p.
       dqip_same_shape obs padded quotient ==>
       dqip_value obs padded (w2i sx - w2i sy + (1 : int)) =
         dqip_value obs quotient (w2i sx - w2i sy + w2i adjust) ==>
       dqip_qr_post
         obs original_x padded divisor remainder sx sy)`;

val dqip_one_limb_branch_def = Define `
  dqip_one_limb_branch
      obs (sy : word32) (sx : word32)
      (x : 'p) (y : 'p) (q : 'p) <=>
    dqip_access_at obs y (dqip_offset obs y) /\
    let divisor = dqip_pelts obs y (dqip_offset obs y) in
      (dqip_valid obs x (w2i sx) /\
       dqip_valid obs q (w2i sx) /\
       dqip_writable obs q = T /\
       (0 : int) < w2i sx /\
       (0 : int) < dqip_uint divisor) /\
      (!q1 : 'p.
         dqip_same_shape obs q1 q ==>
         !remainder_limb : word64.
           dqip_value obs x (w2i sx) =
               dqip_value obs q1 (w2i sx) * dqip_uint divisor +
                 dqip_uint remainder_limb /\
           dqip_uint remainder_limb < dqip_uint divisor ==>
           (dqip_access_at obs x (dqip_offset obs x) /\
            dqip_writable obs x = T) /\
           (!x1 : 'p.
              dqip_same_shape obs x1 x ==>
              dqip_map_updated_at
                obs x1 x (dqip_offset obs x1) remainder_limb ==>
              dqip_qr_post obs x q1 y x1 sx sy))`;

val dqip_div2_preconditions_def = Define `
  dqip_div2_preconditions
      obs (dividend : 'p) (divisor : 'p) (quotient : 'p)
      (total : word32) <=>
    (2 : int) <= w2i total /\
    dqip_valid obs dividend (w2i total) /\
    dqip_valid obs divisor (2 : int) /\
    dqip_valid obs quotient (w2i total - (2 : int)) /\
    dqip_half_radix <=
      dqip_uint
        (dqip_pelts obs divisor (dqip_offset obs divisor + (1 : int))) /\
    dqip_writable obs quotient = T /\
    dqip_writable obs dividend = T`;

val dqip_div2_direct_continuation_def = Define `
  dqip_div2_direct_continuation
      obs (sx : word32) (sy : word32) (total : word32)
      (original_x : 'p) (divisor : 'p)
      (quotient : 'p) (dividend : 'p) <=>
    !remainder q1 : 'p.
      dqip_same_shape obs remainder dividend ==>
      dqip_same_shape obs q1 quotient ==>
      !qh : word64.
        dqip_division_premise
          obs dividend q1 divisor remainder
          (w2i total) (2 : int) qh ==>
        (dqip_valid obs remainder (w2i sy) /\
         dqip_valid obs original_x (w2i sy) /\
         dqip_writable obs original_x = T) /\
        (!x1 : 'p.
           dqip_same_shape obs x1 original_x ==>
           dqip_copied_range
             obs x1 remainder original_x (w2i sy) ==>
           dqip_qr_post obs original_x q1 divisor x1 sx sy)`;

val dqip_copy_append_zero_div2_def = Define `
  dqip_copy_append_zero_div2
      obs (sx : word32) (sy : word32)
      (original_x : 'p) (divisor : 'p)
      (quotient : 'p) (scratch : 'p) <=>
    !copied : 'p.
      dqip_same_shape obs copied scratch ==>
      dqip_copied_range obs copied original_x scratch (w2i sx) ==>
      (dqip_access_at
         obs copied (dqip_offset obs copied + w2i sx) /\
       dqip_writable obs copied = T) /\
      (!extended : 'p.
         dqip_same_shape obs extended copied ==>
         dqip_updated_at_and_stored
           obs extended copied
           (dqip_offset obs extended + w2i sx) (0w : word64) ==>
         dqip_int32_in_bounds (w2i sx + (1 : int)) /\
         (!total : word32.
            w2i total = w2i sx + (1 : int) ==>
            dqip_div2_preconditions
              obs extended divisor quotient total /\
            dqip_div2_direct_continuation
              obs sx sy total original_x divisor quotient extended))`;

val dqip_two_limb_unshifted_def = Define `
  dqip_two_limb_unshifted
      obs (sx : word32) (sy : word32)
      (x : 'p) (y : 'p) (q : 'p) (nx : 'p) <=>
    (dqip_valid obs x (w2i sx) /\
     dqip_valid obs nx (w2i sx) /\
     dqip_writable obs nx = T) /\
    dqip_copy_append_zero_div2 obs sx sy x y q nx`;

val dqip_two_limb_shifted_div_continuation_def = Define `
  dqip_two_limb_shifted_div_continuation
      obs (sx : word32) (sy : word32) (clz : word32) (scale : int)
      (original_x : 'p) (original_y : 'p) (q : 'p)
      (normalized_divisor : 'p) (normalized_dividend : 'p)
      (total : word32) <=>
    dqip_div2_preconditions
      obs normalized_dividend normalized_divisor q total /\
    (!remainder q1 : 'p.
       dqip_same_shape obs remainder normalized_dividend ==>
       dqip_same_shape obs q1 q ==>
       !qh : word64.
         dqip_division_premise
           obs normalized_dividend q1 normalized_divisor remainder
           (w2i total) (2 : int) qh ==>
         (0 : int) <= w2i clz /\
         (!shift : word64.
            dqip_uint shift = w2i clz ==>
            (dqip_valid obs remainder (w2i sy) /\
             dqip_valid obs original_x (w2i sy) /\
             dqip_shift_count_bounds shift /\
             (0 : int) < w2i sy /\
             dqip_writable obs original_x = T) /\
            (!restored : 'p.
               dqip_same_shape obs restored original_x ==>
               !discarded : word64.
                 dqip_uint discarded +
                     dqip_radix * dqip_value obs restored (w2i sy) =
                   dqip_value obs remainder (w2i sy) *
                     dqip_power (2 : int)
                       ((64 : int) - dqip_uint shift) ==>
                 dqip_value obs remainder (2 : int) =
                     scale * dqip_value obs restored (2 : int) /\
                 (dqip_value obs remainder (2 : int) =
                    scale * dqip_value obs restored (2 : int) ==>
                  dqip_qr_post
                    obs original_x q1 original_y restored sx sy))))`;

val dqip_two_limb_shifted_def = Define `
  dqip_two_limb_shifted
      obs (sx : word32) (sy : word32) (clz : word32) (scale : int)
      (x : 'p) (y : 'p) (q : 'p) (nx : 'p) (ny : 'p) <=>
    (0 : int) <= w2i clz /\
    (!shift_y : word64.
       dqip_uint shift_y = w2i clz ==>
       (dqip_shift_count_bounds shift_y /\
        dqip_valid obs ny (w2i sy) /\
        dqip_valid obs y (w2i sy) /\
        dqip_writable obs ny = T /\
        (0 : int) < w2i sy) /\
       (!normalized_y : 'p.
          dqip_same_shape obs normalized_y ny ==>
          !carry_y : word64.
            dqip_value obs normalized_y (w2i sy) +
                dqip_power dqip_radix (w2i sy) * dqip_uint carry_y =
              dqip_value obs y (w2i sy) *
                dqip_power (2 : int) (dqip_uint shift_y) ==>
            (dqip_normalized obs normalized_y sy /\
             dqip_value obs normalized_y (w2i sy) =
               scale * dqip_value obs y (w2i sy)) /\
            (dqip_normalized obs normalized_y sy /\
             dqip_value obs normalized_y (w2i sy) =
               scale * dqip_value obs y (w2i sy) ==>
             (0 : int) <= w2i clz /\
             (!shift_x : word64.
                dqip_uint shift_x = w2i clz ==>
                (dqip_shift_count_bounds shift_x /\
                 dqip_valid obs nx (w2i sx) /\
                 dqip_valid obs x (w2i sx) /\
                 dqip_writable obs nx = T /\
                 (0 : int) < w2i sx) /\
                (!shifted_x : 'p.
                   dqip_same_shape obs shifted_x nx ==>
                   !high : word64.
                     dqip_value obs shifted_x (w2i sx) +
                         dqip_power dqip_radix (w2i sx) * dqip_uint high =
                       dqip_value obs x (w2i sx) *
                         dqip_power (2 : int) (dqip_uint shift_x) ==>
                     (dqip_access_at
                        obs shifted_x
                        (dqip_offset obs shifted_x + w2i sx) /\
                      dqip_writable obs shifted_x = T) /\
                     (!extended : 'p.
                        dqip_same_shape obs extended shifted_x ==>
                        dqip_updated_at_and_stored
                          obs extended shifted_x
                          (dqip_offset obs extended + w2i sx) high ==>
                        dqip_value obs extended (w2i sx + (1 : int)) =
                            scale * dqip_value obs x (w2i sx) /\
                        (dqip_value obs extended (w2i sx + (1 : int)) =
                           scale * dqip_value obs x (w2i sx) ==>
                         dqip_int32_in_bounds (w2i sx + (1 : int)) /\
                         (!total : word32.
                            w2i total = w2i sx + (1 : int) ==>
                            dqip_two_limb_shifted_div_continuation
                              obs sx sy clz scale x y q
                              normalized_y extended total))))))))`;

val dqip_two_limb_case_def = Define `
  dqip_two_limb_case
      obs (sx : word32) (sy : word32)
      (x : 'p) (y : 'p) (q : 'p) (nx : 'p) (ny : 'p) <=>
    dqip_int32_in_bounds (w2i sy - (1 : int)) /\
    (!top_index : word32.
       w2i top_index = w2i sy - (1 : int) ==>
       dqip_access_at
         obs y (dqip_offset obs y + w2i top_index) /\
       let most_significant =
         dqip_pelts obs y (dqip_offset obs y + w2i top_index)
       in
         (0 : int) < dqip_uint most_significant /\
         (!clz : word32.
            dqip_clz_conditions most_significant clz ==>
            let scale = dqip_power (2 : int) (w2i clz)
            in
              !zero_flag : bool.
                dqip_word_flag clz (0w : word32) zero_flag ==>
                if zero_flag = T then
                  dqip_two_limb_unshifted obs sx sy x y q nx
                else
                  dqip_two_limb_shifted
                    obs sx sy clz scale x y q nx ny))`;

val dqip_general_div_preconditions_def = Define `
  dqip_general_div_preconditions
      obs (sy : word32) (total : word32)
      (dividend : 'p) (divisor : 'p) (quotient : 'p) <=>
    ((3 : int) <= w2i sy /\ w2i sy <= w2i total) /\
    dqip_valid obs dividend (w2i total) /\
    dqip_valid obs divisor (w2i sy) /\
    dqip_valid obs quotient (w2i total - w2i sy) /\
    dqip_writable obs quotient = T /\
    dqip_writable obs dividend = T /\
    dqip_normalized obs divisor sy`;

val dqip_general_direct_continuation_def = Define `
  dqip_general_direct_continuation
      obs (sx : word32) (sy : word32)
      (adjust : word32) (total : word32)
      (x : 'p) (divisor : 'p) (q : 'p) (dividend : 'p) <=>
    !remainder q1 : 'p.
      dqip_same_shape obs remainder dividend ==>
      dqip_same_shape obs q1 q ==>
      !qh : word64.
        dqip_division_premise
          obs dividend q1 divisor remainder
          (w2i total) (w2i sy) qh ==>
        (dqip_valid obs remainder (w2i sy) /\
         dqip_valid obs x (w2i sy) /\
         dqip_writable obs x = T) /\
        (!restored : 'p.
           dqip_same_shape obs restored x ==>
           dqip_copied_range obs restored remainder x (w2i sy) ==>
           dqip_finish_with_padding
             obs x q1 divisor restored sx sy adjust)`;

val dqip_general_unshifted_def = Define `
  dqip_general_unshifted
      obs (sx : word32) (sy : word32) (adjust : word32)
      (x : 'p) (y : 'p) (q : 'p) (nx : 'p) <=>
    (dqip_valid obs x (w2i sx) /\
     dqip_valid obs nx (w2i sx) /\
     dqip_writable obs nx = T) /\
    (!copied : 'p.
       dqip_same_shape obs copied nx ==>
       dqip_copied_range obs copied x nx (w2i sx) ==>
       (dqip_access_at
          obs copied (dqip_offset obs copied + w2i sx) /\
        dqip_writable obs copied = T) /\
       (!extended : 'p.
          dqip_same_shape obs extended copied ==>
          dqip_updated_at_and_stored
            obs extended copied
            (dqip_offset obs extended + w2i sx) (0w : word64) ==>
          dqip_int32_in_bounds (w2i sx + w2i adjust) /\
          (!total : word32.
             w2i total = w2i sx + w2i adjust ==>
             dqip_general_div_preconditions obs sy total extended y q /\
             dqip_general_direct_continuation
               obs sx sy adjust total x y q extended)))`;

val dqip_general_shifted_continuation_def = Define `
  dqip_general_shifted_continuation
      obs (sx : word32) (sy : word32)
      (adjust : word32) (clz : word32)
      (total : word32) (scale : int)
      (x : 'p) (y : 'p) (q : 'p)
      (normalized_dividend : 'p) (normalized_divisor : 'p) <=>
    !remainder q1 : 'p.
      dqip_same_shape obs remainder normalized_dividend ==>
      dqip_same_shape obs q1 q ==>
      !qh : word64.
        dqip_division_premise
          obs normalized_dividend q1 normalized_divisor remainder
          (w2i total) (w2i sy) qh ==>
        (0 : int) <= w2i clz /\
        (!shift : word64.
           dqip_uint shift = w2i clz ==>
           (dqip_valid obs remainder (w2i sy) /\
            dqip_valid obs x (w2i sy) /\
            dqip_shift_count_bounds shift /\
            (0 : int) < w2i sy /\
            dqip_writable obs x = T) /\
           (!restored : 'p.
              dqip_same_shape obs restored x ==>
              !discarded : word64.
                dqip_uint discarded +
                    dqip_radix * dqip_value obs restored (w2i sy) =
                  dqip_value obs remainder (w2i sy) *
                    dqip_power (2 : int)
                      ((64 : int) - dqip_uint shift) ==>
                dqip_value obs remainder (w2i sy) =
                    scale * dqip_value obs restored (w2i sy) /\
                (dqip_value obs remainder (w2i sy) =
                   scale * dqip_value obs restored (w2i sy) ==>
                 dqip_finish_with_padding
                   obs x q1 y restored sx sy adjust)))`;

val dqip_general_shifted_def = Define `
  dqip_general_shifted
      obs (sx : word32) (sy : word32)
      (adjust : word32) (clz : word32) (scale : int)
      (x : 'p) (y : 'p) (q : 'p) (nx : 'p) (ny : 'p) <=>
    (0 : int) <= w2i clz /\
    (!shift_y : word64.
       dqip_uint shift_y = w2i clz ==>
       (dqip_shift_count_bounds shift_y /\
        dqip_valid obs ny (w2i sy) /\
        dqip_valid obs y (w2i sy) /\
        dqip_writable obs ny = T /\
        (0 : int) < w2i sy) /\
       (!normalized_y : 'p.
          dqip_same_shape obs normalized_y ny ==>
          !carry_y : word64.
            dqip_value obs normalized_y (w2i sy) +
                dqip_power dqip_radix (w2i sy) * dqip_uint carry_y =
              dqip_value obs y (w2i sy) *
                dqip_power (2 : int) (dqip_uint shift_y) ==>
            (0 : int) <= w2i clz /\
            (!shift_x : word64.
               dqip_uint shift_x = w2i clz ==>
               (dqip_shift_count_bounds shift_x /\
                dqip_valid obs nx (w2i sx) /\
                dqip_valid obs x (w2i sx) /\
                dqip_writable obs nx = T /\
                (0 : int) < w2i sx) /\
               (!shifted_x : 'p.
                  dqip_same_shape obs shifted_x nx ==>
                  !high : word64.
                    dqip_value obs shifted_x (w2i sx) +
                        dqip_power dqip_radix (w2i sx) * dqip_uint high =
                      dqip_value obs x (w2i sx) *
                        dqip_power (2 : int) (dqip_uint shift_x) ==>
                    (dqip_access_at
                       obs shifted_x
                       (dqip_offset obs shifted_x + w2i sx) /\
                     dqip_writable obs shifted_x = T) /\
                    (!extended : 'p.
                       dqip_same_shape obs extended shifted_x ==>
                       dqip_updated_at_and_stored
                         obs extended shifted_x
                         (dqip_offset obs extended + w2i sx) high ==>
                       (!adjust_one : bool.
                          dqip_word_flag
                            adjust (1w : word32) adjust_one ==>
                          dqip_int32_in_bounds (w2i sx + w2i adjust) /\
                          (!total : word32.
                             w2i total = w2i sx + w2i adjust ==>
                             dqip_general_div_preconditions
                               obs sy total extended normalized_y q /\
                             dqip_general_shifted_continuation
                               obs sx sy adjust clz total scale
                               x y q extended normalized_y)))))))`;

val dqip_general_clz_case_def = Define `
  dqip_general_clz_case
      obs (sx : word32) (sy : word32) (adjust : word32)
      (x : 'p) (y : 'p) (q : 'p) (nx : 'p) (ny : 'p)
      (most_significant : word64) <=>
    !clz : word32.
      dqip_clz_conditions most_significant clz ==>
      let scale = dqip_power (2 : int) (w2i clz)
      in
        !zero_flag : bool.
          dqip_word_flag clz (0w : word32) zero_flag ==>
          if zero_flag = T then
            dqip_general_unshifted obs sx sy adjust x y q nx
          else
            dqip_general_shifted
              obs sx sy adjust clz scale x y q nx ny`;

val dqip_general_case_def = Define `
  dqip_general_case
      obs (sx : word32) (sy : word32)
      (x : 'p) (y : 'p) (q : 'p) (nx : 'p) (ny : 'p) <=>
    dqip_int32_in_bounds (w2i sy - (1 : int)) /\
    (!y_top : word32.
       w2i y_top = w2i sy - (1 : int) ==>
       dqip_access_at obs y (dqip_offset obs y + w2i y_top) /\
       dqip_int32_in_bounds (w2i sx - (1 : int)) /\
       (!x_top : word32.
          w2i x_top = w2i sx - (1 : int) ==>
          dqip_access_at obs x (dqip_offset obs x + w2i x_top) /\
          (!adjust : word32.
             (if dqip_uint
                    (dqip_pelts obs y
                      (dqip_offset obs y + w2i y_top)) <=
                  dqip_uint
                    (dqip_pelts obs x
                      (dqip_offset obs x + w2i x_top))
              then adjust = (1w : word32)
              else adjust = (0w : word32)) ==>
             dqip_int32_in_bounds (w2i sy - (1 : int)) /\
             (!y_top_again : word32.
                w2i y_top_again = w2i sy - (1 : int) ==>
                dqip_access_at
                  obs y (dqip_offset obs y + w2i y_top_again) /\
                let most_significant =
                  dqip_pelts obs y
                    (dqip_offset obs y + w2i y_top_again)
                in
                  (0 : int) < dqip_uint most_significant /\
                  dqip_general_clz_case
                    obs sx sy adjust x y q nx ny
                    most_significant))))`;

val dqip_non_one_limb_branch_def = Define `
  dqip_non_one_limb_branch
      obs (sy : word32) (sx : word32)
      (x : 'p) (y : 'p) (q : 'p) (nx : 'p) (ny : 'p) <=>
    !two_flag : bool.
      dqip_word_flag sy (2w : word32) two_flag ==>
      if two_flag = T then
        dqip_two_limb_case obs sx sy x y q nx ny
      else
        dqip_general_case obs sx sy x y q nx ny`;

val div_Div_div_qr_in_placeqtvc_statement =
  ``!obs :
       'p -> (num # (int -> word64)) #
         (int # (int # (int # (bool # 'z)))).
    !sy sx : word32.
    !x y q nx ny : 'p.
    !one_flag : bool.
      (1 : int) <= w2i sy ==>
      w2i sy <= w2i sx ==>
      w2i sx <= (2147483647 : int) - (1 : int) ==>
      dqip_valid obs x (w2i sx) ==>
      dqip_valid obs y (w2i sy) ==>
      dqip_valid obs q (w2i sx - w2i sy + (1 : int)) ==>
      dqip_valid obs nx (w2i sx + (1 : int)) ==>
      dqip_valid obs ny (w2i sy) ==>
      dqip_writable obs q = T ==>
      dqip_writable obs x = T ==>
      dqip_writable obs nx = T ==>
      dqip_writable obs ny = T ==>
      (0 : int) <
        dqip_uint
          (dqip_pelts obs y
            (dqip_offset obs y + w2i sy - (1 : int))) ==>
      dqip_word_flag sy (1w : word32) one_flag ==>
      if one_flag = T then
        dqip_one_limb_branch obs sy sx x y q
      else
        dqip_non_one_limb_branch obs sy sx x y q nx ny``;
