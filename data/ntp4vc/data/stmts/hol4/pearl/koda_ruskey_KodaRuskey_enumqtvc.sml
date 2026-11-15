(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/koda_ruskey_KodaRuskey_enumqtvc: the recursive enumeration
  verification condition for Koda-Ruskey forest colorings, stack transitions,
  and accumulated distinct solutions. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val _ = Datatype `
  kr_color =
      KRWhite
    | KRBlack
`;

val _ = Datatype `
  kr_forest =
      KRE
    | KRN int kr_forest kr_forest
`;

val kr_to_num_def = Define `
  kr_to_num (z : int) = if z < 0 then 0 else Num z`;

val kr_get_def = Define `
  kr_get (xs : kr_color list) (i : int) =
    if kr_to_num i < LENGTH xs then EL (kr_to_num i) xs else ARB`;

val kr_get_coloring_def = Define `
  kr_get_coloring (xs : (int -> kr_color) list) (i : int) =
    if kr_to_num i < LENGTH xs then EL (kr_to_num i) xs else ARB`;

val kr_size_forest_def = Define `
  (kr_size_forest KRE = (0 : int)) /\
  (kr_size_forest (KRN x f1 f2) =
     (1 : int) + kr_size_forest f1 + kr_size_forest f2)`;

val kr_mem_forest_def = Define `
  (kr_mem_forest (n : int) KRE = F) /\
  (kr_mem_forest n (KRN i f1 f2) =
     (i = n \/ kr_mem_forest n f1 \/ kr_mem_forest n f2))`;

val kr_between_range_forest_def = Define `
  kr_between_range_forest (i : int) (j : int) f <=>
    !n : int.
      kr_mem_forest n f ==> i <= n /\ n < j`;

val kr_disjoint_def = Define `
  kr_disjoint f1 f2 <=>
    !x : int.
      kr_mem_forest x f1 ==> ~kr_mem_forest x f2`;

val kr_no_repeated_forest_def = Define `
  (kr_no_repeated_forest KRE = T) /\
  (kr_no_repeated_forest (KRN i f1 f2) =
     (kr_no_repeated_forest f1 /\
      kr_no_repeated_forest f2 /\
      ~kr_mem_forest i f1 /\
      ~kr_mem_forest i f2 /\
      kr_disjoint f1 f2))`;

val kr_valid_nums_forest_def = Define `
  kr_valid_nums_forest f (n : int) <=>
    kr_between_range_forest (0 : int) n f /\
    kr_no_repeated_forest f`;

val kr_white_forest_def = Define `
  (kr_white_forest KRE (c : int -> kr_color) = T) /\
  (kr_white_forest (KRN i f1 f2) c =
     (c i = KRWhite /\
      kr_white_forest f1 c /\
      kr_white_forest f2 c))`;

val kr_valid_coloring_def = Define `
  (kr_valid_coloring KRE (c : int -> kr_color) = T) /\
  (kr_valid_coloring (KRN i f1 f2) c =
     (kr_valid_coloring f2 c /\
      case c i of
        KRWhite => kr_white_forest f1 c
      | KRBlack => kr_valid_coloring f1 c))`;

val kr_count_forest_def = Define `
  (kr_count_forest KRE = (1 : int)) /\
  (kr_count_forest (KRN x f1 f2) =
     ((1 : int) + kr_count_forest f1) * kr_count_forest f2)`;

val kr_eq_coloring_def = Define `
  kr_eq_coloring (n : int) c1 c2 <=>
    !i : int.
      (0 : int) <= i /\ i < n ==> c1 i = c2 i`;

val kr_mem_stack_def = Define `
  (kr_mem_stack (n : int) ([] : kr_forest list) = F) /\
  (kr_mem_stack n (f :: tl) =
     (kr_mem_forest n f \/ kr_mem_stack n tl))`;

val kr_size_stack_def = Define `
  (kr_size_stack ([] : kr_forest list) = (0 : int)) /\
  (kr_size_stack (f :: st1) =
     kr_size_forest f + kr_size_stack st1)`;

val kr_even_forest_def = Define `
  (kr_even_forest KRE = F) /\
  (kr_even_forest (KRN x f1 f2) =
     (~kr_even_forest f1 \/ kr_even_forest f2))`;

val kr_final_forest_def = Define `
  (kr_final_forest KRE (c : int -> kr_color) = T) /\
  (kr_final_forest (KRN i f1 f2) c =
     (c i = KRBlack /\
      kr_final_forest f1 c /\
      if ~kr_even_forest f1 then
        kr_white_forest f2 c
      else
        kr_final_forest f2 c))`;

val kr_any_forest_def = Define `
  kr_any_forest f c <=>
    kr_white_forest f c \/ kr_final_forest f c`;

val kr_unchanged_def = Define `
  kr_unchanged st c1 c2 <=>
    !i : int.
      kr_mem_stack i st ==> c1 i = c2 i`;

val kr_inverse_def = Define `
  (kr_inverse ([] : kr_forest list)
      (c1 : int -> kr_color) (c2 : int -> kr_color) = T) /\
  (kr_inverse (f :: st') c1 c2 =
     ((kr_white_forest f c1 /\ kr_final_forest f c2 \/
       kr_final_forest f c1 /\ kr_white_forest f c2) /\
      if kr_even_forest f then
        kr_unchanged st' c1 c2
      else
        kr_inverse st' c1 c2))`;

val kr_any_stack_def = Define `
  (kr_any_stack ([] : kr_forest list) (c : int -> kr_color) = T) /\
  (kr_any_stack (f :: st1) c =
     (kr_any_forest f c /\ kr_any_stack st1 c))`;

val (kr_sub_rules, kr_sub_ind, kr_sub_cases) =
  Hol_reln `
    (!f c.
       kr_sub [f] f (c : int -> kr_color)) /\
    (!st f2 c i f1.
       kr_sub st f2 c ==>
       kr_sub st (KRN i f1 f2) c) /\
    (!st f1 c i f2.
       kr_sub st f1 c /\ c i = KRBlack ==>
       kr_sub (st ++ [f2]) (KRN i f1 f2) c)
  `;

val kr_count_stack_def = Define `
  (kr_count_stack ([] : kr_forest list) = (1 : int)) /\
  (kr_count_stack (f :: st') =
     kr_count_forest f * kr_count_stack st')`;

val kr_stored_solutions_def = Define `
  kr_stored_solutions f0 bits st v1 v2 <=>
    let n = kr_size_forest f0 in
    let start = &(LENGTH v1) in
    let stop = &(LENGTH v2) in
      stop - start = kr_count_stack st /\
      (!j : int.
         (0 : int) <= j /\ j < start ==>
         kr_eq_coloring n
           (kr_get_coloring v2 j)
           (kr_get_coloring v1 j)) /\
      (!j : int.
         start <= j /\ j < stop ==>
         kr_valid_coloring f0 (kr_get_coloring v2 j) /\
         (!i : int.
            (0 : int) <= i /\ i < n ==>
            ~kr_mem_stack i st ==>
            kr_get_coloring v2 j i = bits i) /\
         (!k : int.
            start <= k /\ k < stop ==>
            ~(j = k) ==>
            ~kr_eq_coloring n
              (kr_get_coloring v2 j)
              (kr_get_coloring v2 k)))`;

val kr_progress_def = Define `
  kr_progress old_st new_st <=>
    ((0 : int) <= kr_size_stack old_st /\
     kr_size_stack new_st < kr_size_stack old_st \/
     kr_size_stack old_st = kr_size_stack new_st /\
     (case old_st of
        [] => F
      | _ :: tail => tail = new_st))`;

val kr_ready_def = Define `
  kr_ready f0 bits st <=>
    kr_size_forest f0 = &(LENGTH bits) /\
    kr_valid_nums_forest f0 (&(LENGTH bits)) /\
    kr_sub st f0 (kr_get bits) /\
    kr_any_stack st (kr_get bits) /\
    kr_valid_coloring f0 (kr_get bits)`;

val kr_step_ready_def = Define `
  kr_step_ready old_st f0 bits new_st <=>
    kr_progress old_st new_st /\
    kr_size_forest f0 = &(LENGTH bits) /\
    kr_valid_nums_forest f0 (&(LENGTH bits)) /\
    kr_sub new_st f0 (kr_get bits) /\
    kr_any_stack new_st (kr_get bits) /\
    kr_valid_coloring f0 (kr_get bits)`;

val kr_step_ready_nonempty_def = Define `
  kr_step_ready_nonempty old_st f0 bits new_st <=>
    kr_progress old_st new_st /\
    kr_size_forest f0 = &(LENGTH bits) /\
    kr_valid_nums_forest f0 (&(LENGTH bits)) /\
    kr_sub new_st f0 (kr_get bits) /\
    new_st <> [] /\
    kr_any_stack new_st (kr_get bits) /\
    kr_valid_coloring f0 (kr_get bits)`;

val kr_recursive_result_def = Define `
  kr_recursive_result f0 base_bits cur_st visited_start
      result_bits visited_result <=>
    (!i : int.
       ~kr_mem_stack i cur_st ==>
       kr_get result_bits i = kr_get base_bits i) /\
    kr_inverse cur_st (kr_get base_bits) (kr_get result_bits) /\
    kr_valid_coloring f0 (kr_get result_bits) /\
    kr_stored_solutions f0 (kr_get result_bits) cur_st
      visited_start visited_result`;

val kr_continuation_def = Define `
  kr_continuation f0 root_bits root_st root_visited
      base_bits cur_st visited_start <=>
    !result_bits visited_result.
      LENGTH result_bits = LENGTH base_bits ==>
      kr_recursive_result f0 base_bits cur_st visited_start
        result_bits visited_result ==>
      kr_recursive_result f0 root_bits root_st root_visited
        result_bits visited_result`;

val koda_ruskey_KodaRuskey_enumqtvc_statement =
  ``!f0 : kr_forest.
    !bits : kr_color list.
    !st : kr_forest list.
    !visited : (int -> kr_color) list.
      kr_size_forest f0 = &(LENGTH bits) ==>
      kr_valid_nums_forest f0 (&(LENGTH bits)) ==>
      kr_sub st f0 (kr_get bits) ==>
      st <> [] ==>
      kr_any_stack st (kr_get bits) ==>
      kr_valid_coloring f0 (kr_get bits) ==>
      case st of
        [] => F
      | KRE :: st' =>
          (case st' of
             [] =>
               let o1 = kr_get bits in
               let o2 = visited ++ [o1] in
                 (&(LENGTH o2) =
                    (1 : int) + &(LENGTH visited) /\
                  EL (LENGTH visited) o2 = o1 /\
                  (!i : int.
                     (0 : int) <= i /\
                     i < &(LENGTH visited) ==>
                     kr_get_coloring o2 i =
                     kr_get_coloring visited i))
                 ==>
                 kr_inverse st (kr_get bits) (kr_get bits) /\
                 kr_valid_coloring f0 (kr_get bits) /\
                 kr_stored_solutions f0 (kr_get bits) st
                   visited o2
           | _ =>
               kr_step_ready_nonempty st f0 bits st' /\
               kr_continuation f0 bits st visited bits st' visited)
      | KRN i f1 f2 :: st' =>
          ((0 : int) <= i /\ i < &(LENGTH bits)) /\
          if kr_get bits i = KRWhite then
            let o1 = f2 :: st' in
              kr_step_ready st f0 bits o1 /\
              (!bits1 visited1.
                 LENGTH bits1 = LENGTH bits ==>
                 kr_recursive_result f0 bits o1 visited
                   bits1 visited1 ==>
                 let o2 = KRBlack in
                   ((0 : int) <= i /\ i < &(LENGTH bits1)) /\
                   (LENGTH (LUPDATE o2 (kr_to_num i) bits1) =
                      LENGTH bits1 ==>
                    (!j : int.
                       (0 : int) <= j /\ j < &(LENGTH bits1) ==>
                       kr_get (LUPDATE o2 (kr_to_num i) bits1) j =
                         (if j = i then o2 else kr_get bits1 j)) ==>
                    let o3 = f1 :: f2 :: st' in
                      kr_step_ready st f0
                        (LUPDATE o2 (kr_to_num i) bits1) o3 /\
                      kr_continuation f0 bits st visited
                        (LUPDATE o2 (kr_to_num i) bits1)
                        o3 visited1))
          else
            let o1 = f1 :: f2 :: st' in
              kr_step_ready st f0 bits o1 /\
              (!bits1 visited1.
                 LENGTH bits1 = LENGTH bits ==>
                 kr_recursive_result f0 bits o1 visited
                   bits1 visited1 ==>
                 let o2 = KRWhite in
                   ((0 : int) <= i /\ i < &(LENGTH bits1)) /\
                   (LENGTH (LUPDATE o2 (kr_to_num i) bits1) =
                      LENGTH bits1 ==>
                    (!j : int.
                       (0 : int) <= j /\ j < &(LENGTH bits1) ==>
                       kr_get (LUPDATE o2 (kr_to_num i) bits1) j =
                         (if j = i then o2 else kr_get bits1 j)) ==>
                    let o3 = f2 :: st' in
                      kr_step_ready st f0
                        (LUPDATE o2 (kr_to_num i) bits1) o3 /\
                      kr_continuation f0 bits st visited
                        (LUPDATE o2 (kr_to_num i) bits1)
                        o3 visited1))``;
