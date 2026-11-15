(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/koda_ruskey_KodaRuskey_mainqtvc: the main verification condition for
  enumerating all valid Koda-Ruskey forest colorings exactly once from the
  initial all-white coloring. This file contains no proof.
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

val koda_ruskey_KodaRuskey_mainqtvc_statement =
  ``!f0 : kr_forest.
    !bits : kr_color list.
      kr_white_forest f0 (kr_get bits) ==>
      kr_size_forest f0 = &(LENGTH bits) ==>
      kr_valid_nums_forest f0 (&(LENGTH bits)) ==>
      let o1 = [f0] in
        (kr_size_forest f0 = &(LENGTH bits) /\
         kr_valid_nums_forest f0 (&(LENGTH bits)) /\
         kr_sub o1 f0 (kr_get bits) /\
         kr_any_stack o1 (kr_get bits) /\
         kr_valid_coloring f0 (kr_get bits)) /\
        (!bits1 : kr_color list.
         !visited : (int -> kr_color) list.
           LENGTH bits1 = LENGTH bits ==>
           ((!i : int.
               ~kr_mem_stack i o1 ==>
               kr_get bits1 i = kr_get bits i) /\
            kr_inverse o1 (kr_get bits) (kr_get bits1) /\
            kr_valid_coloring f0 (kr_get bits1) /\
            kr_stored_solutions f0 (kr_get bits1) o1 [] visited) ==>
           &(LENGTH visited) = kr_count_forest f0 /\
           (let n = &(LENGTH visited) in
              !j : int.
                (0 : int) <= j /\ j < n ==>
                kr_valid_coloring f0 (kr_get_coloring visited j) /\
                (!k : int.
                   (0 : int) <= k /\ k < n ==>
                   ~(j = k) ==>
                   ~kr_eq_coloring (&(LENGTH bits1))
                     (kr_get_coloring visited j)
                     (kr_get_coloring visited k))))``;
