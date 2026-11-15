(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2024_challenge1_Top_smart_array_copy_0qtvc:
  the verification condition for smart array copying by shuffled fixed-size
  subsegments, including permutation pairs, nested element-copy loop
  invariants, list updates, and the final remainder. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val sac0_to_num_def = Define `
  sac0_to_num (i : int) =
    if i < (0 : int) then 0 else Num i`;

val sac0_int_nth_def = Define `
  sac0_int_nth (a : int list) (i : int) =
    if sac0_to_num i < LENGTH a then
      EL (sac0_to_num i) a
    else
      (0 : int)`;

val sac0_nth_def = Define `
  sac0_nth (a : 'a list) (i : int) =
    if sac0_to_num i < LENGTH a then
      EL (sac0_to_num i) a
    else
      ARB`;

val sac0_set_def = Define `
  sac0_set (a : 'a list) (i : int) (x : 'a) =
    LUPDATE x (sac0_to_num i) a`;

val sac0_update_def = Define `
  sac0_update (f : int -> 'a) (i : int) (x : 'a) =
    \j : int. if j = i then x else f j`;

val sac0_permutation_def = Define `
  sac0_permutation (l : int) (p : int list) <=>
    ((0 : int) <= l /\ l <= &(LENGTH p)) /\
    (!i : int.
       (0 : int) <= i /\ i < l ==>
       (0 : int) <= sac0_int_nth p i /\
       sac0_int_nth p i < l) /\
    (!i j : int.
       (0 : int) <= i /\ i < l ==>
       (0 : int) <= j /\ j < l ==>
       ~(i = j) ==>
       ~(sac0_int_nth p i = sac0_int_nth p j))`;

val sac0_permutation_pair_def = Define `
  sac0_permutation_pair
      (l : int) (p : int list) (invp : int list) <=>
    sac0_permutation l p /\
    sac0_permutation l invp /\
    (!i : int.
       (0 : int) <= i /\ i < l ==>
       sac0_int_nth p (sac0_int_nth invp i) = i) /\
    (!i : int.
       (0 : int) <= i /\ i < l ==>
       sac0_int_nth invp (sac0_int_nth p i) = i)`;

val sac0_valid_chunk_def = Define `
  sac0_valid_chunk
      (a : 'a list) (ofs : int) (len : int) <=>
    (0 : int) <= ofs /\
    ofs <= ofs + len /\
    ofs + len <= &(LENGTH a)`;

val sac0_copy_def = Define `
  sac0_copy
      (src : 'a list) (dst : 'a list) (ofs : int) (len : int) <=>
    sac0_valid_chunk src ofs len /\
    LENGTH src = LENGTH dst /\
    (!i : int.
       ofs <= i /\ i < ofs + len ==>
       sac0_nth dst i = sac0_nth src i)`;

val sac0_all_shuffled_chunks_def = Define `
  sac0_all_shuffled_chunks
      (src : 'a list)
      (dst : 'a list)
      (start : int)
      (sigma : int list)
      (k : int)
      (upper : int) <=>
    !j' : int.
      (0 : int) <= j' /\ j' < upper ==>
      sac0_copy
        src dst (start + sac0_int_nth sigma j' * k) k`;

val sac0_list_set_function_equal_def = Define `
  sac0_list_set_function_equal
      (a : 'a list) (i : int) (x : 'a) <=>
    (\j : int. sac0_nth (sac0_set a i x) j) =
    sac0_update (\j : int. sac0_nth a j) i x`;

val sac0_i_step_conclusion_def = Define `
  sac0_i_step_conclusion
      (src : 'a list)
      (dst3 : 'a list)
      (start : int)
      (startj : int)
      (sigma : int list)
      (k : int)
      (s : int)
      (m : int)
      (j : int)
      (i : int) <=>
    let index = startj + i in
    let value = sac0_nth src index in
    let updated = sac0_set dst3 index value in
      ((0 : int) <= index /\ index < &(LENGTH src)) /\
      ((0 : int) <= index /\ index < &(LENGTH dst3)) /\
      (LENGTH updated = LENGTH dst3 ==>
       sac0_list_set_function_equal dst3 index value ==>
       sac0_copy src updated (0 : int) (s * m) /\
       sac0_all_shuffled_chunks
         src updated start sigma k j /\
       sac0_copy src updated startj (i + (1 : int)))`;

val sac0_all_i_steps_def = Define `
  sac0_all_i_steps
      (src : 'a list)
      (dst3 : 'a list)
      (start : int)
      (startj : int)
      (sigma : int list)
      (k : int)
      (s : int)
      (m : int)
      (j : int)
      (o3 : int) <=>
    !i : int.
      ((0 : int) <= i /\ i <= o3) /\
      sac0_copy src dst3 (0 : int) (s * m) /\
      sac0_all_shuffled_chunks
        src dst3 start sigma k j /\
      sac0_copy src dst3 startj i ==>
      sac0_i_step_conclusion
        src dst3 start startj sigma k s m j i`;

val sac0_dst3_body_def = Define `
  sac0_dst3_body
      (src : 'a list)
      (dst3 : 'a list)
      (start : int)
      (startj : int)
      (sigma : int list)
      (k : int)
      (s : int)
      (m : int)
      (j : int)
      (o3 : int) <=>
    sac0_all_i_steps
      src dst3 start startj sigma k s m j o3 /\
    (sac0_copy src dst3 (0 : int) (s * m) /\
     sac0_all_shuffled_chunks
       src dst3 start sigma k j /\
     sac0_copy src dst3 startj (o3 + (1 : int)) ==>
     sac0_copy src dst3 (0 : int) (s * m) /\
     sac0_all_shuffled_chunks
       src dst3 start sigma k (j + (1 : int)))`;

val sac0_all_dst3_loops_def = Define `
  sac0_all_dst3_loops
      (src : 'a list)
      (dst2 : 'a list)
      (start : int)
      (startj : int)
      (sigma : int list)
      (k : int)
      (s : int)
      (m : int)
      (j : int)
      (o3 : int) <=>
    !dst3 : 'a list.
      LENGTH dst3 = LENGTH dst2 ==>
      sac0_dst3_body
        src dst3 start startj sigma k s m j o3`;

val sac0_j_step_conclusion_def = Define `
  sac0_j_step_conclusion
      (src : 'a list)
      (dst2 : 'a list)
      (start : int)
      (sigma : int list)
      (k : int)
      (s : int)
      (m : int)
      (j : int) <=>
    ((0 : int) <= j /\ j < &(LENGTH sigma)) /\
    let startj = start + sac0_int_nth sigma j * k in
    let o3 = k - (1 : int) in
      (((0 : int) <= o3 + (1 : int) ==>
        (sac0_copy src dst2 (0 : int) (s * m) /\
         sac0_all_shuffled_chunks
           src dst2 start sigma k j /\
         sac0_copy src dst2 startj (0 : int)) /\
        sac0_all_dst3_loops
          src dst2 start startj sigma k s m j o3) /\
       (o3 + (1 : int) < (0 : int) ==>
        sac0_copy src dst2 (0 : int) (s * m) /\
        sac0_all_shuffled_chunks
          src dst2 start sigma k (j + (1 : int))))`;

val sac0_all_j_steps_def = Define `
  sac0_all_j_steps
      (src : 'a list)
      (dst2 : 'a list)
      (start : int)
      (sigma : int list)
      (k : int)
      (s : int)
      (m : int)
      (o2 : int) <=>
    !j : int.
      ((0 : int) <= j /\ j <= o2) /\
      sac0_copy src dst2 (0 : int) (s * m) /\
      sac0_all_shuffled_chunks
        src dst2 start sigma k j ==>
      sac0_j_step_conclusion
        src dst2 start sigma k s m j`;

val sac0_dst2_body_def = Define `
  sac0_dst2_body
      (src : 'a list)
      (dst2 : 'a list)
      (start : int)
      (sigma : int list)
      (k : int)
      (s : int)
      (m : int)
      (o2 : int) <=>
    sac0_all_j_steps src dst2 start sigma k s m o2 /\
    (sac0_copy src dst2 (0 : int) (s * m) /\
     sac0_all_shuffled_chunks
       src dst2 start sigma k (o2 + (1 : int)) ==>
     sac0_copy
       src dst2 (0 : int) ((s + (1 : int)) * m))`;

val sac0_all_dst2_loops_def = Define `
  sac0_all_dst2_loops
      (src : 'a list)
      (dst1 : 'a list)
      (start : int)
      (sigma : int list)
      (k : int)
      (s : int)
      (m : int)
      (o2 : int) <=>
    !dst2 : 'a list.
      LENGTH dst2 = LENGTH dst1 ==>
      sac0_dst2_body src dst2 start sigma k s m o2`;

val sac0_sigma_body_def = Define `
  sac0_sigma_body
      (src : 'a list)
      (dst1 : 'a list)
      (start : int)
      (sigma : int list)
      (k : int)
      (l : int)
      (s : int)
      (m : int) <=>
    let o2 = l - (1 : int) in
      (((0 : int) <= o2 + (1 : int) ==>
        (sac0_copy src dst1 (0 : int) (s * m) /\
         sac0_all_shuffled_chunks
           src dst1 start sigma k (0 : int)) /\
        sac0_all_dst2_loops
          src dst1 start sigma k s m o2) /\
       (o2 + (1 : int) < (0 : int) ==>
        sac0_copy
          src dst1 (0 : int) ((s + (1 : int)) * m)))`;

val sac0_all_permutations_def = Define `
  sac0_all_permutations
      (src : 'a list)
      (dst1 : 'a list)
      (start : int)
      (k : int)
      (l : int)
      (s : int)
      (m : int) <=>
    !sigma invsigma : int list.
      ((LENGTH sigma = LENGTH invsigma /\
        &(LENGTH invsigma) = l) /\
       sac0_permutation_pair l sigma invsigma) ==>
      sac0_sigma_body src dst1 start sigma k l s m`;

val sac0_s_body_def = Define `
  sac0_s_body
      (src : 'a list)
      (dst1 : 'a list)
      (k : int)
      (l : int)
      (s : int)
      (m : int) <=>
    let start = s * m in
      (0 : int) < l /\
      sac0_all_permutations src dst1 start k l s m`;

val sac0_all_s_loops_def = Define `
  sac0_all_s_loops
      (src : 'a list)
      (dst1 : 'a list)
      (k : int)
      (l : int)
      (m : int)
      (o1 : int) <=>
    !s : int.
      ((0 : int) <= s /\ s <= o1) /\
      sac0_copy src dst1 (0 : int) (s * m) ==>
      sac0_s_body src dst1 k l s m`;

val sac0_remainder_i_step_conclusion_def = Define `
  sac0_remainder_i_step_conclusion
      (src : 'a list)
      (dst2 : 'a list)
      (last : int)
      (q : int)
      (m : int)
      (i : int) <=>
    let index = last + i in
    let value = sac0_nth src index in
    let updated = sac0_set dst2 index value in
      ((0 : int) <= index /\ index < &(LENGTH src)) /\
      ((0 : int) <= index /\ index < &(LENGTH dst2)) /\
      (LENGTH updated = LENGTH dst2 ==>
       sac0_list_set_function_equal dst2 index value ==>
       sac0_copy src updated (0 : int) (q * m) /\
       sac0_copy src updated last (i + (1 : int)))`;

val sac0_all_remainder_i_steps_def = Define `
  sac0_all_remainder_i_steps
      (src : 'a list)
      (dst2 : 'a list)
      (last : int)
      (q : int)
      (m : int)
      (o2 : int) <=>
    !i : int.
      ((0 : int) <= i /\ i <= o2) /\
      sac0_copy src dst2 (0 : int) (q * m) /\
      sac0_copy src dst2 last i ==>
      sac0_remainder_i_step_conclusion
        src dst2 last q m i`;

val sac0_remainder_dst2_body_def = Define `
  sac0_remainder_dst2_body
      (src : 'a list)
      (dst2 : 'a list)
      (last : int)
      (q : int)
      (m : int)
      (o2 : int)
      (full_length : int) <=>
    sac0_all_remainder_i_steps
      src dst2 last q m o2 /\
    (sac0_copy src dst2 (0 : int) (q * m) /\
     sac0_copy src dst2 last (o2 + (1 : int)) ==>
     sac0_copy src dst2 (0 : int) full_length)`;

val sac0_all_remainder_dst2_loops_def = Define `
  sac0_all_remainder_dst2_loops
      (src : 'a list)
      (old : 'a list)
      (last : int)
      (q : int)
      (m : int)
      (o2 : int)
      (full_length : int) <=>
    !dst2 : 'a list.
      LENGTH dst2 = LENGTH old ==>
      sac0_remainder_dst2_body
        src dst2 last q m o2 full_length`;

val sac0_remainder_body_def = Define `
  sac0_remainder_body
      (src : 'a list)
      (old : 'a list)
      (q : int)
      (m : int)
      (r : int)
      (full_length : int) <=>
    let last = q * m in
    let o2 = r - (1 : int) in
      (((0 : int) <= o2 + (1 : int) ==>
        (sac0_copy src old (0 : int) (q * m) /\
         sac0_copy src old last (0 : int)) /\
        sac0_all_remainder_dst2_loops
          src old last q m o2 full_length) /\
       (o2 + (1 : int) < (0 : int) ==>
        sac0_copy src old (0 : int) full_length))`;

val sac0_dst1_body_def = Define `
  sac0_dst1_body
      (src : 'a list)
      (dst1 : 'a list)
      (k : int)
      (l : int)
      (q : int)
      (r : int)
      (m : int)
      (o1 : int)
      (full_length : int) <=>
    sac0_all_s_loops src dst1 k l m o1 /\
    (sac0_copy
       src dst1 (0 : int) ((o1 + (1 : int)) * m) ==>
     sac0_remainder_body
       src dst1 q m r full_length)`;

val sac0_all_dst1_loops_def = Define `
  sac0_all_dst1_loops
      (src : 'a list)
      (dst : 'a list)
      (k : int)
      (l : int)
      (q : int)
      (r : int)
      (m : int)
      (o1 : int)
      (full_length : int) <=>
    !dst1 : 'a list.
      LENGTH dst1 = LENGTH dst ==>
      sac0_dst1_body
        src dst1 k l q r m o1 full_length`;

val sac0_main_conclusion_def = Define `
  sac0_main_conclusion
      (src : 'a list)
      (dst : 'a list)
      (k : int)
      (l : int)
      (q : int)
      (r : int) <=>
    let m = k * l in
    let o1 = q - (1 : int) in
    let full_length = &(LENGTH dst) in
      (((0 : int) <= o1 + (1 : int) ==>
        sac0_copy src dst (0 : int) ((0 : int) * m) /\
        sac0_all_dst1_loops
          src dst k l q r m o1 full_length) /\
       (o1 + (1 : int) < (0 : int) ==>
        sac0_remainder_body
          src dst q m r full_length))`;

val verifythis_2024_challenge1_Top_smart_array_copy_0qtvc_statement =
  ``!src : 'a list.
    !dst : 'a list.
    !k l q r : int.
      LENGTH src = LENGTH dst ==>
      (0 : int) < &(LENGTH dst) ==>
      (0 : int) < k ==>
      (0 : int) < l ==>
      (0 : int) <= q ==>
      (0 : int) <= r ==>
      r < k * l ==>
      &(LENGTH dst) = q * k * l + r ==>
      sac0_main_conclusion src dst k l q r``;
