(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_shear_sortqtvc: the verification
  condition for in-place integer-matrix ShearSort, including logarithmic
  rounds, alternating row order, column order, threshold propagation, and
  multiset preservation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory pairTheory;

val _ = type_abbrev
  ("ss_matrix", ``:int # (int # (int -> int -> int))``);

val _ = type_abbrev
  ("ss_bounds", ``:int # int``);

val ss_to_num_def = Define `
  ss_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val ss_rows_def = Define `
  ss_rows (m : ss_matrix) = FST m`;

val ss_columns_def = Define `
  ss_columns (m : ss_matrix) = FST (SND m)`;

val ss_elts_def = Define `
  ss_elts (m : ss_matrix) = SND (SND m)`;

val ss_matrix_ok_def = Define `
  ss_matrix_ok (m : ss_matrix) <=>
    (0 : int) <= ss_rows m /\ (0 : int) <= ss_columns m`;

val ss_power_def = Define `
  ss_power (base : int) (exponent : int) =
    base ** ss_to_num exponent`;

val ss_div_two_def = Define `
  ss_div_two (z : int) = z / (2 : int)`;

val ss_mod_two_def = Define `
  ss_mod_two (z : int) = z % (2 : int)`;

val ss_count_def = Define `
  ss_count (predicate : int -> bool) (lower : int) (upper : int) =
    &(LENGTH
        (FILTER predicate
          (GENLIST
            (\offset : num. lower + &offset)
            (ss_to_num (upper - lower)))))`;

val ss_below_count_def = Define `
  ss_below_count
      (e : int -> int -> int)
      (column : int)
      (value : int)
      (lower : int)
      (upper : int) =
    ss_count (\row. e row column <= value) lower upper`;

val ss_above_count_def = Define `
  ss_above_count
      (e : int -> int -> int)
      (column : int)
      (value : int)
      (lower : int)
      (upper : int) =
    ss_count (\row. value < e row column) lower upper`;

val ss_occurrences_def = Define `
  ss_occurrences
      (value : int)
      (f : int -> int)
      (lower : int)
      (upper : int) =
    ss_count (\index. f index = value) lower upper`;

val ss_mocc_def = Define `
  ss_mocc
      (value : int)
      (e : int -> int -> int)
      (row_count : int)
      (column_count : int) =
    &(LENGTH
        (FILTER
          (\indices : num # num.
            e (&(FST indices)) (&(SND indices)) = value)
          (FLAT
            (GENLIST
              (\row : num.
                GENLIST
                  (\column : num. (row,column))
                  (ss_to_num column_count))
              (ss_to_num row_count)))))`;

val ss_map_permut_def = Define `
  ss_map_permut
      (first_map : int -> int)
      (second_map : int -> int)
      (lower : int)
      (upper : int) <=>
    !value : int.
      ss_occurrences value first_map lower upper =
      ss_occurrences value second_map lower upper`;

val ss_dimensions_def = Define `
  ss_dimensions (current : ss_matrix) (previous : ss_matrix) <=>
    ss_rows current = ss_rows previous /\
    ss_columns current = ss_columns previous`;

val ss_zones_def = Define `
  ss_zones
      (zeros : int -> int)
      (ones : int -> int)
      (width : int)
      (current : ss_matrix)
      (n : int)
      (c : int) <=>
    (!value : int.
      (0 : int) <= zeros value /\
      zeros value <= ones value /\
      ones value <= n) /\
    (!value : int.
      ones value <= zeros value + width) /\
    (!value i j : int.
      (((0 : int) <= i /\ i < zeros value) /\
       ((0 : int) <= j /\ j < c)) ==>
      ss_elts current i j <= value) /\
    (!value i j : int.
      ((ones value <= i /\ i < n) /\
       ((0 : int) <= j /\ j < c)) ==>
      value < ss_elts current i j)`;

val ss_extreme_zones_def = Define `
  ss_extreme_zones
      (width : int)
      (current : ss_matrix)
      (n : int)
      (c : int) <=>
    ss_zones
      (\value : int. (0 : int))
      (\value : int. n)
      width current n c`;

val ss_cross_rows_def = Define `
  ss_cross_rows (current : ss_matrix) (n : int) (c : int) <=>
    !i j1 j2 k : int.
      ((((0 : int) <= i /\ i < k /\ k < n) /\
        ((0 : int) <= j1 /\ j1 < c)) /\
       ((0 : int) <= j2 /\ j2 < c)) ==>
      ss_elts current i j1 <= ss_elts current k j2`;

val ss_snake_rows_def = Define `
  ss_snake_rows (current : ss_matrix) (n : int) (c : int) <=>
    !i j k : int.
      (((0 : int) <= i /\ i < n) /\
       ((0 : int) <= j /\ j <= k /\ k < c)) ==>
      if ss_mod_two i = (0 : int) then
        ss_elts current i j <= ss_elts current i k
      else
        ss_elts current i k <= ss_elts current i j`;

val ss_column_sorted_def = Define `
  ss_column_sorted (current : ss_matrix) (n : int) (c : int) <=>
    !i j k : int.
      (((0 : int) <= i /\ i <= k /\ k < n) /\
       ((0 : int) <= j /\ j < c)) ==>
      ss_elts current i j <= ss_elts current k j`;

val ss_row_permuted_def = Define `
  ss_row_permuted (current : ss_matrix) (previous : ss_matrix) <=>
    !i : int.
      ((0 : int) <= i /\ i < ss_rows current) ==>
      ss_map_permut
        (ss_elts current i)
        (ss_elts previous i)
        (0 : int)
        (ss_columns current)`;

val ss_column_permuted_def = Define `
  ss_column_permuted (current : ss_matrix) (previous : ss_matrix) <=>
    !j : int.
      ((0 : int) <= j /\ j < ss_columns current) ==>
      ss_map_permut
        (\i. ss_elts current i j)
        (\i. ss_elts previous i j)
        (0 : int)
        (ss_rows current)`;

val ss_preserves_occurrences_def = Define `
  ss_preserves_occurrences
      (original : ss_matrix)
      (current : ss_matrix)
      (n : int)
      (c : int) <=>
    !value : int.
      ss_mocc value (ss_elts original) n c =
      ss_mocc value (ss_elts current) n c`;

val ss_power_bounds_def = Define `
  ss_power_bounds (k : int) (exponent : int) (n : int) <=>
    (k - (1 : int)) * ss_power (2 : int) exponent < n /\
    n <= k * ss_power (2 : int) exponent`;

val ss_final_matrix_post_def = Define `
  ss_final_matrix_post
      (original : ss_matrix)
      (current : ss_matrix) <=>
    ss_cross_rows current (ss_rows current) (ss_columns current) /\
    ss_snake_rows current (ss_rows current) (ss_columns current) /\
    ss_preserves_occurrences
      original current (ss_rows current) (ss_columns current)`;

val ss_ascending_def = Define `
  ss_ascending (row : int -> int) (c : int) <=>
    !j k : int.
      ((0 : int) <= j /\ j <= k /\ k < c) ==>
      row j <= row k`;

val ss_descending_def = Define `
  ss_descending (row : int -> int) (c : int) <=>
    !j k : int.
      ((0 : int) <= j /\ j <= k /\ k < c) ==>
      row k <= row j`;

val ss_or_below_def = Define `
  ss_or_below
      (first_row : int -> int)
      (second_row : int -> int)
      (value : int)
      (c : int) <=>
    !i : int.
      ((0 : int) <= i /\ i < c) ==>
      first_row i <= value \/ second_row i <= value`;

val ss_or_above_def = Define `
  ss_or_above
      (first_row : int -> int)
      (second_row : int -> int)
      (value : int)
      (c : int) <=>
    !i : int.
      ((0 : int) <= i /\ i < c) ==>
      value < first_row i \/ value < second_row i`;

val ss_comparator_result_symmetry_def = Define `
  ss_comparator_result_symmetry
      (r1 : int -> int)
      (r2 : int -> int)
      (value : int)
      (c : int) <=>
    !result : bool.
      ((result ==> ss_or_below r2 r1 value c) /\
       (~result ==> ss_or_above r2 r1 value c)) ==>
      (result ==> ss_or_below r1 r2 value c) /\
      (~result ==> ss_or_above r1 r2 value c)`;

val ss_comparator_scan_def = Define `
  ss_comparator_scan
      (r1 : int -> int)
      (r2 : int -> int)
      (value : int)
      (c : int) <=>
    !i : int.
      (((0 : int) <= i /\ i <= c) /\
       (!j : int.
         ((0 : int) <= j /\ j < i) ==>
         r1 j <= value /\ value < r2 j)) ==>
      !outcome : bool.
        (if ~(i = c) then
           if r1 i <= value then outcome = (value < r2 i)
           else outcome = F
         else
           outcome = F) ==>
        if outcome then
          (((0 : int) <= c - i /\ c - (i + (1 : int)) < c - i) /\
           ((0 : int) <= i + (1 : int) /\ i + (1 : int) <= c) /\
           (!j : int.
             ((0 : int) <= j /\ j < i + (1 : int)) ==>
             r1 j <= value /\ value < r2 j))
        else
          (!result : bool.
            (if i = c then result = T
             else result = (r2 i <= value)) ==>
            (result ==> ss_or_below r1 r2 value c) /\
            (~result ==> ss_or_above r1 r2 value c))`;

val ss_comparator_vc_def = Define `
  ss_comparator_vc (c : int) (value : int) <=>
    !r1 r2 : int -> int.
    !orientation : bool.
      ((!j k : int.
         ((0 : int) <= j /\ j <= k /\ k < c) ==>
         if orientation then r1 j <= r1 k else r1 k <= r1 j) /\
       (!j k : int.
         ((0 : int) <= j /\ j <= k /\ k < c) ==>
         if orientation then r2 k <= r2 j else r2 j <= r2 k)) ==>
      if ~orientation then
        ((((0 : int) <= (if orientation then (0 : int) else (1 : int)) /\
           (0 : int) < (if orientation then (0 : int) else (1 : int))) /\
          ss_ascending r2 c /\
          ss_descending r1 c) /\
         ss_comparator_result_symmetry r1 r2 value c)
      else
        ((((0 : int) <= (0 : int) /\ (0 : int) <= c) /\
          (!j : int.
            ((0 : int) <= j /\ j < (0 : int)) ==>
            r1 j <= value /\ value < r2 j)) /\
         ss_comparator_scan r1 r2 value c)`;

val ss_selection_invariant_def = Define `
  ss_selection_invariant
      (e : int -> int -> int)
      (value : int)
      (z : int)
      (upper : int)
      (index : int)
      (no : int)
      (nz : int)
      (n : int)
      (c : int) <=>
    (z <= index /\ index <= upper) /\
    (z <= nz /\ no <= upper) /\
    index - z = (2 : int) * ((nz - z) + (upper - no)) /\
    (!j : int.
      ((0 : int) <= j /\ j < c) ==>
      nz <= ss_below_count e j value (0 : int) index /\
      n - no <=
        ss_above_count e j value (0 : int) index +
        ss_above_count e j value upper n)`;

val ss_selection_initial_def = Define `
  ss_selection_initial
      (e : int -> int -> int)
      (value : int)
      (z : int)
      (upper : int)
      (n : int)
      (c : int) <=>
    (z <= z /\ z <= upper) /\
    (z <= z /\ upper <= upper) /\
    z - z = (2 : int) * ((z - z) + (upper - upper)) /\
    (!j : int.
      ((0 : int) <= j /\ j < c) ==>
      z <= ss_below_count e j value (0 : int) z /\
      n - upper <=
        ss_above_count e j value (0 : int) z +
        ss_above_count e j value upper n)`;

val ss_selection_exit_def = Define `
  ss_selection_exit
      (e : int -> int -> int)
      (value : int)
      (nz : int)
      (no : int)
      (kd : int)
      (n : int)
      (c : int) <=>
    ((0 : int) <= nz /\ nz <= no /\ no <= n) /\
    no <= nz + kd /\
    (!j : int.
      ((0 : int) <= j /\ j < c) ==>
      nz <= ss_below_count e j value (0 : int) n /\
      n - no <= ss_above_count e j value (0 : int) n)`;

val ss_selection_pair_step_def = Define `
  ss_selection_pair_step
      (e : int -> int -> int)
      (value : int)
      (z : int)
      (upper : int)
      (index : int)
      (no : int)
      (nz : int)
      (n : int)
      (c : int) <=>
    let parity = ss_mod_two index in
    let next_row = e (index + (1 : int)) in
    let this_row = e index in
      ((if parity = (0 : int) then
          ss_ascending this_row c
        else
          ss_descending this_row c) /\
       (if parity = (0 : int) then
          ss_descending next_row c
        else
          ss_ascending next_row c)) /\
      (!outcome : bool.
        ((outcome ==> ss_or_below this_row next_row value c) /\
         (~outcome ==> ss_or_above this_row next_row value c)) ==>
        if outcome then
          (((0 : int) <= upper - index /\
            upper - (index + (2 : int)) < upper - index) /\
           (z <= index + (2 : int) /\ index + (2 : int) <= upper) /\
           (z <= nz + (1 : int) /\ no <= upper) /\
           index + (2 : int) - z =
             (2 : int) * (((nz + (1 : int)) - z) + (upper - no)) /\
           (!j : int.
             ((0 : int) <= j /\ j < c) ==>
             nz + (1 : int) <=
               ss_below_count e j value (0 : int) (index + (2 : int)) /\
             n - no <=
               ss_above_count e j value
                 (0 : int) (index + (2 : int)) +
               ss_above_count e j value upper n))
        else
          (((0 : int) <= upper - index /\
            upper - (index + (2 : int)) < upper - index) /\
           (z <= index + (2 : int) /\ index + (2 : int) <= upper) /\
           (z <= nz /\ no - (1 : int) <= upper) /\
           index + (2 : int) - z =
             (2 : int) * ((nz - z) + (upper - (no - (1 : int)))) /\
           (!j : int.
             ((0 : int) <= j /\ j < c) ==>
             nz <=
               ss_below_count e j value (0 : int) (index + (2 : int)) /\
             n - (no - (1 : int)) <=
               ss_above_count e j value
                 (0 : int) (index + (2 : int)) +
               ss_above_count e j value upper n)))`;

val ss_selection_loop_def = Define `
  ss_selection_loop
      (e : int -> int -> int)
      (value : int)
      (z : int)
      (upper : int)
      (kd : int)
      (n : int)
      (c : int) <=>
    !index no nz : int.
      ss_selection_invariant e value z upper index no nz n c ==>
      if index + (1 : int) < upper then
        ss_comparator_vc c value /\
        (2 : int) <> (0 : int) /\
        ss_selection_pair_step e value z upper index no nz n c
      else
        ss_selection_exit e value nz no kd n c`;

val ss_nzo_property_def = Define `
  ss_nzo_property
      (e : int -> int -> int)
      (value : int)
      (kd : int)
      (n : int)
      (c : int)
      (bounds : ss_bounds) <=>
    let nz = FST bounds in
    let no = SND bounds in
      ((0 : int) <= nz /\ nz <= no /\ no <= n) /\
      no <= nz + kd /\
      (!j : int.
        ((0 : int) <= j /\ j < c) ==>
        nz <= ss_below_count e j value (0 : int) n /\
        n - no <= ss_above_count e j value (0 : int) n)`;

val ss_below_column_progress_def = Define `
  ss_below_column_progress
      (current : ss_matrix)
      (n : int)
      (c : int) <=>
    !value i j : int.
      ((((0 : int) <= i /\ i < n) /\
        ((0 : int) <
           ss_below_count
             (ss_elts current) j value (i + (1 : int)) n /\
         (0 : int) <= j /\ j < c)) /\
       value < ss_elts current i j) ==>
      let next = i + (1 : int) in
        ((0 : int) <= n - i /\ n - next < n - i) /\
        ((0 : int) <= next /\ next < n) /\
        ((0 : int) <
           ss_below_count
             (ss_elts current) j value (next + (1 : int)) n /\
         (0 : int) <= j /\ j < c) /\
        value < ss_elts current next j`;

val ss_above_column_progress_def = Define `
  ss_above_column_progress
      (current : ss_matrix)
      (n : int)
      (c : int) <=>
    !value i j : int.
      ((((0 : int) <= i /\ i < n) /\
        ((0 : int) <
           ss_above_count (ss_elts current) j value (0 : int) i /\
         (0 : int) <= j /\ j < c)) /\
       ss_elts current i j <= value) ==>
      let previous = i - (1 : int) in
        ((0 : int) <= i /\ previous < i) /\
        ((0 : int) <= previous /\ previous < n) /\
        ((0 : int) <
           ss_above_count
             (ss_elts current) j value (0 : int) previous /\
         (0 : int) <= j /\ j < c) /\
        ss_elts current previous j <= value`;

val ss_column_progress_def = Define `
  ss_column_progress (current : ss_matrix) (n : int) (c : int) <=>
    ss_below_column_progress current n c /\
    ss_above_column_progress current n c`;

val ss_after_column_sort_def = Define `
  ss_after_column_sort
      (original : ss_matrix)
      (current : ss_matrix)
      (newz : int -> int)
      (newo : int -> int)
      (kd : int)
      (n : int)
      (c : int)
      (l : int)
      (ind : int) <=>
    ss_column_progress current n c /\
    ss_zones newz newo kd current n c /\
    (0 : int) < kd /\
    ss_power_bounds kd (ind + (1 : int)) n /\
    (l < ind + (1 : int) ==> ss_snake_rows current n c) /\
    ss_preserves_occurrences original current n c`;

val ss_after_nzo_def = Define `
  ss_after_nzo
      (original : ss_matrix)
      (row_sorted : ss_matrix)
      (zeros : int -> int)
      (ones : int -> int)
      (nzo : int -> ss_bounds)
      (kd : int)
      (n : int)
      (c : int)
      (l : int)
      (ind : int) <=>
    !value : int.
      let bounds = nzo value in
        ss_nzo_property (ss_elts row_sorted) value kd n c bounds ==>
        ((!result : int.
           result = FST bounds ==>
           result = FST (nzo value)) /\
         (!newz : int -> int.
           (!value1 : int. newz value1 = FST (nzo value1)) ==>
           !value1 : int.
             let bounds1 = nzo value1 in
               ss_nzo_property
                 (ss_elts row_sorted) value1 kd n c bounds1 ==>
               ((!result : int.
                  result = SND bounds1 ==>
                  result = SND (nzo value1)) /\
                (!newo : int -> int.
                  (!value2 : int. newo value2 = SND (nzo value2)) ==>
                  (ind = l ==>
                    ss_zones zeros ones (1 : int) row_sorted n c) /\
                  ((ind = l ==>
                    ss_cross_rows row_sorted n c) ==>
                   !column_sorted : ss_matrix.
                     ss_matrix_ok column_sorted ==>
                     ss_dimensions column_sorted row_sorted ==>
                     (ss_column_permuted column_sorted row_sorted /\
                      ss_column_sorted
                        column_sorted
                        (ss_rows column_sorted)
                        (ss_columns column_sorted)) ==>
                     ss_after_column_sort
                       original column_sorted newz newo
                       kd n c l ind)))))`;

val ss_selection_vc_def = Define `
  ss_selection_vc
      (original : ss_matrix)
      (row_sorted : ss_matrix)
      (zeros : int -> int)
      (ones : int -> int)
      (k : int)
      (n : int)
      (c : int)
      (l : int)
      (ind : int) <=>
    let e = ss_elts row_sorted in
    let kd = ss_div_two (k + (1 : int)) in
      (2 : int) <> (0 : int) /\
      ((!value : int.
         let z = zeros value in
         let upper = ones value in
           ss_selection_initial e value z upper n c /\
           ss_selection_loop e value z upper kd n c) /\
       (!nzo : int -> ss_bounds.
         (!value : int.
           ss_nzo_property e value kd n c (nzo value)) ==>
         ss_after_nzo
           original row_sorted zeros ones nzo kd n c l ind))`;

val ss_outer_invariant_def = Define `
  ss_outer_invariant
      (original : ss_matrix)
      (current : ss_matrix)
      (zeros : int -> int)
      (ones : int -> int)
      (k : int)
      (n : int)
      (c : int)
      (l : int)
      (ind : int) <=>
    ((0 : int) <= ind /\ ind <= l) /\
    ss_zones zeros ones k current n c /\
    (0 : int) < k /\
    ss_power_bounds k ind n /\
    (l < ind ==> ss_snake_rows current n c) /\
    ss_preserves_occurrences original current n c`;

val ss_row_round_def = Define `
  ss_row_round
      (original : ss_matrix)
      (current : ss_matrix)
      (zeros : int -> int)
      (ones : int -> int)
      (k : int)
      (n : int)
      (c : int)
      (l : int)
      (ind : int) <=>
    !row_sorted : ss_matrix.
      ss_matrix_ok row_sorted ==>
      ss_dimensions row_sorted current ==>
      (ss_row_permuted row_sorted current /\
       ss_snake_rows
         row_sorted (ss_rows row_sorted) (ss_columns row_sorted)) ==>
      ss_selection_vc
        original row_sorted zeros ones k n c l ind`;

val ss_outer_exit_invariant_def = Define `
  ss_outer_exit_invariant
      (original : ss_matrix)
      (current : ss_matrix)
      (zeros : int -> int)
      (ones : int -> int)
      (k : int)
      (n : int)
      (c : int)
      (l : int) <=>
    ss_zones zeros ones k current n c /\
    (0 : int) < k /\
    ss_power_bounds k (l + (1 : int)) n /\
    (l < l + (1 : int) ==> ss_snake_rows current n c) /\
    ss_preserves_occurrences original current n c`;

val ss_outer_exit_post_def = Define `
  ss_outer_exit_post
      (original : ss_matrix)
      (current : ss_matrix)
      (zeros : int -> int)
      (ones : int -> int)
      (k : int)
      (n : int)
      (c : int)
      (l : int) <=>
    ss_outer_exit_invariant original current zeros ones k n c l ==>
    ss_zones zeros ones (1 : int) current n c /\
    (ss_cross_rows current n c ==>
      ss_final_matrix_post original current)`;

val ss_outer_body_def = Define `
  ss_outer_body
      (original : ss_matrix)
      (zeros : int -> int)
      (ones : int -> int)
      (k : int)
      (current : ss_matrix)
      (n : int)
      (c : int)
      (l : int) <=>
    !ind : int.
      ss_outer_invariant
        original current zeros ones k n c l ind ==>
      ss_row_round original current zeros ones k n c l ind`;

val ss_initial_outer_invariant_def = Define `
  ss_initial_outer_invariant
      (original : ss_matrix)
      (n : int)
      (c : int)
      (l : int) <=>
    ss_extreme_zones n original n c /\
    (0 : int) < n /\
    ss_power_bounds n (0 : int) n /\
    (l < (0 : int) ==> ss_snake_rows original n c)`;

val ss_width_one_implies_cross_def = Define `
  ss_width_one_implies_cross
      (original : ss_matrix)
      (n : int)
      (c : int) <=>
    !ones zeros : int -> int.
    !current : ss_matrix.
      ss_matrix_ok current ==>
      ss_dimensions current original ==>
      ss_zones zeros ones (1 : int) current n c ==>
      ss_cross_rows current n c`;

val ss_negative_outer_branch_def = Define `
  ss_negative_outer_branch
      (original : ss_matrix)
      (n : int)
      (c : int) <=>
    ss_extreme_zones (1 : int) original n c /\
    (ss_cross_rows original n c ==>
      ss_cross_rows
        original (ss_rows original) (ss_columns original) /\
      ss_snake_rows
        original (ss_rows original) (ss_columns original))`;

val ss_outer_loop_vc_def = Define `
  ss_outer_loop_vc
      (original : ss_matrix)
      (n : int)
      (c : int)
      (l : int) <=>
    ss_width_one_implies_cross original n c /\
    (((0 : int) <= l + (1 : int) ==>
      ss_initial_outer_invariant original n c l /\
      (!ones zeros : int -> int.
       !k : int.
       !current : ss_matrix.
         ss_matrix_ok current ==>
         ss_dimensions current original ==>
         ss_outer_body original zeros ones k current n c l /\
         ss_outer_exit_post
           original current zeros ones k n c l)) /\
     (l + (1 : int) < (0 : int) ==>
      ss_negative_outer_branch original n c))`;

val ss_log_invariant_def = Define `
  ss_log_invariant (p : int) (l : int) (n : int) <=>
    ((0 : int) <= l /\ (0 : int) <= p) /\
    (l <> (0 : int) ==>
      ss_power (2 : int) (l - (1 : int)) <= n) /\
    p * ss_power (2 : int) l < n /\
    n <= ss_power (2 : int) l * (p + (1 : int))`;

val ss_log_step_def = Define `
  ss_log_step (p : int) (l : int) (n : int) <=>
    (2 : int) <> (0 : int) /\
    ((0 : int) <= p /\ ss_div_two p < p) /\
    ((0 : int) <= l + (1 : int) /\ (0 : int) <= ss_div_two p) /\
    (l + (1 : int) <> (0 : int) ==>
      ss_power
        (2 : int) ((l + (1 : int)) - (1 : int)) <= n) /\
    ss_div_two p * ss_power (2 : int) (l + (1 : int)) < n /\
    n <=
      ss_power (2 : int) (l + (1 : int)) *
      (ss_div_two p + (1 : int))`;

val ss_log_loop_vc_def = Define `
  ss_log_loop_vc
      (original : ss_matrix)
      (n : int)
      (c : int) <=>
    !p l : int.
      ss_log_invariant p l n ==>
      if ~(p = (0 : int)) then
        ss_log_step p l n
      else
        ss_outer_loop_vc original n c l`;

val ss_nonempty_matrix_vc_def = Define `
  ss_nonempty_matrix_vc
      (original : ss_matrix)
      (n : int)
      (c : int) <=>
    let last_row = n - (1 : int) in
      (((0 : int) <= (0 : int) /\ (0 : int) <= last_row) /\
       last_row * ss_power (2 : int) (0 : int) < n /\
       n <= ss_power (2 : int) (0 : int) * (last_row + (1 : int))) /\
      ss_log_loop_vc original n c`;

val ss_empty_matrix_vc_def = Define `
  ss_empty_matrix_vc (original : ss_matrix) <=>
    ss_cross_rows original (ss_rows original) (ss_columns original) /\
    ss_snake_rows original (ss_rows original) (ss_columns original)`;

val ss_shear_sort_vc_def = Define `
  ss_shear_sort_vc (original : ss_matrix) <=>
    let n = ss_rows original in
    let c = ss_columns original in
      if ~(n = (0 : int)) then
        ss_nonempty_matrix_vc original n c
      else
        ss_empty_matrix_vc original`;

val verifythis_2021_shearsort_ShearSort_shear_sortqtvc_statement =
  ``!original : ss_matrix.
      ss_matrix_ok original ==>
      ss_shear_sort_vc original``;
