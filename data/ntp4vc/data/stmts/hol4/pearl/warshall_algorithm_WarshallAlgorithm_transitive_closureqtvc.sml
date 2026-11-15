(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/warshall_algorithm_WarshallAlgorithm_transitive_closureqtvc: the
  Warshall transitive-closure verification condition over Boolean matrices,
  including the bounded-path relation and all three loop invariants. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory pairTheory;

val _ = type_abbrev
  ("warshall_matrix", ``:num # (num # (int -> int -> bool))``);

val warshall_rows_def = Define `
  warshall_rows (m : warshall_matrix) = &(FST m)`;

val warshall_columns_def = Define `
  warshall_columns (m : warshall_matrix) = &(FST (SND m))`;

val warshall_elts_def = Define `
  warshall_elts (m : warshall_matrix) = SND (SND m)`;

val warshall_same_shape_def = Define `
  warshall_same_shape
      (a : warshall_matrix) (b : warshall_matrix) <=>
    warshall_rows a = warshall_rows b /\
    warshall_columns a = warshall_columns b`;

val warshall_valid_index_def = Define `
  warshall_valid_index
      (m : warshall_matrix) (i : int) (j : int) <=>
    ((0 : int) <= i /\ i < warshall_rows m) /\
    (0 : int) <= j /\ j < warshall_columns m`;

val warshall_update_entry_def = Define `
  warshall_update_entry
      (a : int -> int -> bool) (i : int) (j : int) (v : bool) =
    \x y. if x = i /\ y = j then v else a x y`;

val (warshall_path_rules,
     warshall_path_ind,
     warshall_path_cases) =
  Hol_reln `
    (!m : warshall_matrix. !i j k : int.
       warshall_elts m i j = T ==>
       warshall_path m i j k) /\
    (!x k : int. !m : warshall_matrix. !i j : int.
       (0 : int) <= x /\
       x < k /\
       warshall_path m i x k /\
       warshall_path m x j k ==>
       warshall_path m i j k)
  `;

val warshall_invariant_def = Define `
  warshall_invariant
      (m : warshall_matrix) (t : warshall_matrix)
      (n : int) (k : int) <=>
    !x y : int.
      (0 : int) <= x /\ x < n ==>
      (0 : int) <= y /\ y < n ==>
      (warshall_elts t x y = T <=>
       warshall_path m x y k)`;

val warshall_row_invariant_def = Define `
  warshall_row_invariant
      (m : warshall_matrix) (t : warshall_matrix)
      (n : int) (k : int) (i : int) <=>
    !x y : int.
      (0 : int) <= x /\ x < n ==>
      (0 : int) <= y /\ y < n ==>
      (warshall_elts t x y = T <=>
       if x < i then
         warshall_path m x y (k + (1 : int))
       else
         warshall_path m x y k)`;

val warshall_column_invariant_def = Define `
  warshall_column_invariant
      (m : warshall_matrix) (t : warshall_matrix)
      (n : int) (k : int) (i : int) (j : int) <=>
    !x y : int.
      (0 : int) <= x /\ x < n ==>
      (0 : int) <= y /\ y < n ==>
      (warshall_elts t x y = T <=>
       if x < i \/ x = i /\ y < j then
         warshall_path m x y (k + (1 : int))
       else
         warshall_path m x y k)`;

val warshall_cell_obligation_def = Define `
  warshall_cell_obligation
      (m : warshall_matrix) (t3 : warshall_matrix)
      (n : int) (k : int) (i : int) (j : int) <=>
    warshall_valid_index t3 i j /\
    let o4 = warshall_elts t3 i j in
      (~(o4 = T) ==>
       warshall_valid_index t3 i k /\
       (warshall_elts t3 i k = T ==>
        warshall_valid_index t3 k j)) /\
      !o5 : bool.
        (if o4 = T then
           o5 = T
         else if warshall_elts t3 i k = T then
           o5 = warshall_elts t3 k j
         else
           o5 = F)
        ==>
        warshall_valid_index t3 i j /\
        !t4 : warshall_matrix.
          warshall_same_shape t4 t3 ==>
          warshall_elts t4 =
            warshall_update_entry (warshall_elts t3) i j o5 ==>
          warshall_column_invariant
            m t4 n k i (j + (1 : int))`;

val warshall_column_loop_def = Define `
  warshall_column_loop
      (m : warshall_matrix) (t2 : warshall_matrix)
      (n : int) (k : int) (i : int) <=>
    let o3 = n - (1 : int) in
      (((0 : int) <= o3 + (1 : int) ==>
        warshall_column_invariant m t2 n k i (0 : int) /\
        !t3 : warshall_matrix.
          warshall_same_shape t3 t2 ==>
          ((!j : int.
              ((0 : int) <= j /\ j <= o3) /\
              warshall_column_invariant m t3 n k i j ==>
              warshall_cell_obligation m t3 n k i j) /\
           (warshall_column_invariant
              m t3 n k i (o3 + (1 : int)) ==>
            warshall_row_invariant
              m t3 n k (i + (1 : int))))) /\
       (o3 + (1 : int) < (0 : int) ==>
        warshall_row_invariant
          m t2 n k (i + (1 : int))))`;

val warshall_row_loop_def = Define `
  warshall_row_loop
      (m : warshall_matrix) (t1 : warshall_matrix)
      (n : int) (k : int) <=>
    let o2 = n - (1 : int) in
      (((0 : int) <= o2 + (1 : int) ==>
        warshall_row_invariant m t1 n k (0 : int) /\
        !t2 : warshall_matrix.
          warshall_same_shape t2 t1 ==>
          ((!i : int.
              ((0 : int) <= i /\ i <= o2) /\
              warshall_row_invariant m t2 n k i ==>
              warshall_column_loop m t2 n k i) /\
           (warshall_row_invariant
              m t2 n k (o2 + (1 : int)) ==>
            warshall_invariant
              m t2 n (k + (1 : int))))) /\
       (o2 + (1 : int) < (0 : int) ==>
        warshall_invariant
          m t1 n (k + (1 : int))))`;

val warshall_outer_loop_def = Define `
  warshall_outer_loop
      (m : warshall_matrix) (t : warshall_matrix) (n : int) <=>
    let o1 = n - (1 : int) in
      (((0 : int) <= o1 + (1 : int) ==>
        warshall_invariant m t n (0 : int) /\
        !t1 : warshall_matrix.
          warshall_same_shape t1 t ==>
          ((!k : int.
              ((0 : int) <= k /\ k <= o1) /\
              warshall_invariant m t1 n k ==>
              warshall_row_loop m t1 n k) /\
           (warshall_invariant m t1 n (o1 + (1 : int)) ==>
            warshall_invariant m t1 n n))) /\
       (o1 + (1 : int) < (0 : int) ==>
        warshall_invariant m t n n))`;

val warshall_algorithm_WarshallAlgorithm_transitive_closureqtvc =
  ``!m t : warshall_matrix.
      warshall_rows m = warshall_columns m ==>
      warshall_rows t = warshall_rows m ==>
      warshall_columns t = warshall_columns m ==>
      (!r : int.
         (0 : int) <= r /\ r < warshall_rows t ==>
         !c : int.
           (0 : int) <= c /\ c < warshall_columns t ==>
           warshall_elts t r c = warshall_elts m r c)
      ==>
      warshall_outer_loop m t (warshall_rows m)``;
