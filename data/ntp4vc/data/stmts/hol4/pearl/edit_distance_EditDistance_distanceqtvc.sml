(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/edit_distance_EditDistance_distanceqtvc: a dynamic-programming edit
  distance verification condition with suffix-based minimum-distance row and
  column invariants. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val ed_to_nat_def = Define `
  ed_to_nat (z : int) = if z < 0 then 0 else Num z`;

val ed_get_def = Define `
  ed_get (xs : int list) (z : int) =
    if ed_to_nat z < LENGTH xs then EL (ed_to_nat z) xs else 0`;

val ed_update_matches_def = Define `
  ed_update_matches (xs : int list) (j : int) (x : int) <=>
    LENGTH (LUPDATE x (ed_to_nat j) xs) = LENGTH xs /\
    (\z : int. ed_get (LUPDATE x (ed_to_nat j) xs) z) =
      (\z : int. if z = j then x else ed_get xs z)`;

val (ed_dist_rules,
     ed_dist_ind,
     ed_dist_cases) =
  Hol_reln `
    ed_dist ([] : 'a list) ([] : 'a list) (0 : int) /\
    (!w1 w2 n a.
       ed_dist w1 w2 n ==>
       ed_dist (a :: w1) w2 (n + (1 : int))) /\
    (!w1 w2 n a.
       ed_dist w1 w2 n ==>
       ed_dist w1 (a :: w2) (n + (1 : int))) /\
    (!w1 w2 n a.
       ed_dist w1 w2 n ==>
       ed_dist (a :: w1) (a :: w2) n)
  `;

val ed_min_dist_def = Define `
  ed_min_dist w1 w2 (n : int) <=>
    ed_dist w1 w2 n /\
    !m : int. ed_dist w1 w2 m ==> n <= m`;

val ed_suffix_def = Define `
  ed_suffix (w : 'a list) (i : int) = DROP (ed_to_nat i) w`;

val ed_min_suffix_def = Define `
  ed_min_suffix w1 w2 (i : int) (j : int) (n : int) <=>
    ed_min_dist (ed_suffix w1 i) (ed_suffix w2 j) n`;

val ed_row_inv_def = Define `
  ed_row_inv w1 w2 (i : int) (n2 : int) (t : int list) <=>
    !j : int.
      0 <= j /\ j <= n2 ==>
      ed_min_suffix w1 w2 i j (ed_get t j)`;

val ed_split_inv_def = Define `
  ed_split_inv
    w1 w2 (i : int) (n2 : int) (j : int) (oldt : int)
    (t : int list) <=>
      (!k : int.
         j < k /\ k <= n2 ==>
         ed_min_suffix w1 w2 i k (ed_get t k)) /\
      (!k : int.
         0 <= k /\ k <= j ==>
         ed_min_suffix w1 w2 (i + 1) k (ed_get t k)) /\
      ed_min_suffix w1 w2 (i + 1) (j + 1) oldt`;

val ed_char_step_def = Define `
  ed_char_step
    w1 w2 (i : int) (n2 : int) (j : int) (oldt : int)
    (t : int list) <=>
      (0 <= j /\ j < &(LENGTH t)) /\
      (0 <= j /\ j < &(LENGTH w2)) /\
      (0 <= i /\ i < &(LENGTH w1)) /\
      if EL (ed_to_nat i) w1 = EL (ed_to_nat j) w2 then
        (0 <= j /\ j < &(LENGTH t)) /\
        (ed_update_matches t j oldt ==>
         ed_split_inv
           w1 w2 i n2 (j - 1) (ed_get t j)
           (LUPDATE oldt (ed_to_nat j) t))
      else
        let o5 = j + 1 in
          (0 <= o5 /\ o5 < &(LENGTH t)) /\
          (0 <= j /\ j < &(LENGTH t)) /\
          let o6 =
            (if ed_get t j <= ed_get t o5
             then ed_get t j
             else ed_get t o5) + 1
          in
            (0 <= j /\ j < &(LENGTH t)) /\
            (ed_update_matches t j o6 ==>
             ed_split_inv
               w1 w2 i n2 (j - 1) (ed_get t j)
               (LUPDATE o6 (ed_to_nat j) t))`;

val ed_row_step_def = Define `
  ed_row_step
    w1 w2 (i : int) (n2 : int) (t : int list) <=>
      (0 <= n2 /\ n2 < &(LENGTH t)) /\
      (0 <= n2 /\ n2 < &(LENGTH t)) /\
      let o3 = ed_get t n2 + 1 in
        (0 <= n2 /\ n2 < &(LENGTH t)) /\
        (ed_update_matches t n2 o3 ==>
         let t0 = LUPDATE o3 (ed_to_nat n2) t in
         let o4 = n2 - 1 in
           (((0 : int) - 1 <= o4 ==>
              ed_split_inv w1 w2 i n2 o4 (ed_get t n2) t0 /\
              !oldt : int. !t1 : int list.
                LENGTH t1 = LENGTH t0 ==>
                ((!j : int.
                    ((j <= o4 /\ 0 <= j) /\
                     ed_split_inv w1 w2 i n2 j oldt t1) ==>
                    ed_char_step w1 w2 i n2 j oldt t1) /\
                 (ed_split_inv
                    w1 w2 i n2 ((0 : int) - 1) oldt t1 ==>
                  ed_row_inv w1 w2 (i - 1 + 1) n2 t1))) /\
            (o4 < (0 : int) - 1 ==>
             ed_row_inv w1 w2 (i - 1 + 1) n2 t0)))`;

val ed_final_def = Define `
  ed_final w1 w2 (t : int list) <=>
    ((0 : int) <= 0 /\ (0 : int) < &(LENGTH t)) /\
    ed_min_dist
      (ed_suffix w1 (0 : int))
      (ed_suffix w2 (0 : int))
      (ed_get t (0 : int))`;

val ed_rows_phase_def = Define `
  ed_rows_phase
    w1 w2 (n1 : int) (n2 : int) (t : int list) <=>
      let o2 = n1 - 1 in
        (((0 : int) - 1 <= o2 ==>
           ed_row_inv w1 w2 (o2 + 1) n2 t /\
           !t1 : int list.
             LENGTH t1 = LENGTH t ==>
             ((!i : int.
                 ((i <= o2 /\ 0 <= i) /\
                  ed_row_inv w1 w2 (i + 1) n2 t1) ==>
                 ed_row_step w1 w2 i n2 t1) /\
              (ed_row_inv w1 w2 ((0 : int) - 1 + 1) n2 t1 ==>
               ed_final w1 w2 t1))) /\
         (o2 < (0 : int) - 1 ==>
          ed_final w1 w2 t))`;

val ed_init_prefix_def = Define `
  ed_init_prefix (n2 : int) (i : int) (t : int list) <=>
    !j : int.
      0 <= j /\ j < i ==>
      ed_get t j = n2 - j`;

val ed_init_phase_def = Define `
  ed_init_phase
    w1 w2 (n1 : int) (n2 : int) (t : int list) <=>
      ed_init_prefix n2 (0 : int) t /\
      !t1 : int list.
        LENGTH t1 = LENGTH t ==>
        ((!i : int.
            ((0 <= i /\ i <= n2) /\
             ed_init_prefix n2 i t1) ==>
            (0 <= i /\ i < &(LENGTH t1)) /\
            let o2 = n2 - i in
              (ed_update_matches t1 i o2 ==>
               ed_init_prefix
                 n2 (i + 1) (LUPDATE o2 (ed_to_nat i) t1))) /\
         (ed_init_prefix n2 (n2 + 1) t1 ==>
          ed_rows_phase w1 w2 n1 n2 t1))`;

val edit_distance_EditDistance_distance_vc =
  ``!w1 : 'a list. !w2 : 'a list.
      let n1 = &(LENGTH w1) in
      let n2 = &(LENGTH w2) in
      let o1 = n2 + (1 : int) in
        (0 : int) <= o1 /\
        !t : int list.
          ((!i : int.
              0 <= i /\ i < o1 ==>
              ed_get t i = (0 : int)) /\
           &(LENGTH t) = o1) ==>
          ((0 <= n2 + 1 ==>
            ed_init_phase w1 w2 n1 n2 t) /\
           (n2 + 1 < 0 ==>
            ed_rows_phase w1 w2 n1 n2 t))``;
