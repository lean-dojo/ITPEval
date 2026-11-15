(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2018_le_rouge_et_le_noir_1_ColoredTiles_enumqtvc:
  the verification condition for enumerating finite valid red-and-black tile
  colorings through nested array updates and loop invariants. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory pairTheory pred_setTheory;

val _ = Datatype `
  ct_color =
      CTRed
    | CTBlack
`;

val ct_to_num_def = Define `
  ct_to_num (z : int) = if z < 0 then 0 else Num z`;

val ct_color_get_def = Define `
  ct_color_get (c : ct_color list) (i : int) =
    if ct_to_num i < LENGTH c then EL (ct_to_num i) c else ARB`;

val ct_tworedneighbors_def = Define `
  ct_tworedneighbors (c : ct_color list) (i : int) <=>
    (ct_color_get c (i - 2) = CTRed /\
     ct_color_get c (i - 1) = CTRed /\
     (2 : int) <= i) \/
    (ct_color_get c (i - 1) = CTRed /\
     ct_color_get c (i + 1) = CTRed /\
     (1 : int) <= i /\
     i <= &(LENGTH c) - 2) \/
    (ct_color_get c (i + 1) = CTRed /\
     ct_color_get c (i + 2) = CTRed /\
     i <= &(LENGTH c) - 3)`;

val ct_valid_def = Define `
  ct_valid (c : ct_color list) <=>
    !i : int.
      (0 : int) <= i /\ i < &(LENGTH c) ==>
      ct_color_get c i = CTRed ==>
      ct_tworedneighbors c i`;

val ct_first_black_tile_def = Define `
  (ct_first_black_tile ([] : ct_color list) = (0 : int)) /\
  (ct_first_black_tile (CTRed :: c) =
     (1 : int) + ct_first_black_tile c) /\
  (ct_first_black_tile (CTBlack :: c) = (0 : int))`;

val ct_black_seq_def = Define `
  ct_black_seq (n : int) =
    GENLIST (K CTBlack) (ct_to_num n)`;

val ct_red_seq_def = Define `
  ct_red_seq (n : int) =
    GENLIST (K CTRed) (ct_to_num n)`;

val ct_addleft_def = Define `
  ct_addleft (nr : int) (c : ct_color list) =
    ct_red_seq nr ++ CTBlack :: c`;

val ct_mapaddleft_def = Define `
  ct_mapaddleft (s : ct_color list set) (nr : int) =
    IMAGE (ct_addleft nr) s`;

val ct_alen_def = Define `
  ct_alen (a : num # (int -> 'a)) = &(FST a)`;

val ct_get_def = Define `
  ct_get (a : num # (int -> 'a)) (i : int) = SND a i`;

val ct_set_def = Define `
  ct_set (a : num # (int -> 'a)) (i : int) (x : 'a) =
    (FST a, \j. if j = i then x else SND a j)`;

val ct_in_bounds_def = Define `
  ct_in_bounds (a : num # (int -> 'a)) (i : int) <=>
    (0 : int) <= i /\ i < ct_alen a`;

val ct_update_ok_def = Define `
  ct_update_ok (a : num # (int -> 'a)) (i : int) (x : 'a) <=>
    ct_alen (ct_set a i x) = ct_alen a /\
    ct_get (ct_set a i x) =
      (\j. if j = i then x else ct_get a j)`;

val ct_array_init_def = Define `
  ct_array_init (a : num # (int -> 'a)) (n : num) (x : 'a) <=>
    ct_alen a = &n /\
    (!i : int.
       (0 : int) <= i /\ i < &n ==>
       ct_get a i = x)`;

val ct_finite_array_def = Define `
  ct_finite_array
      (sets : num # (int -> ct_color list set)) <=>
    !i : int.
      ct_in_bounds sets i ==> FINITE (ct_get sets i)`;

val ct_prefix_inv_def = Define `
  ct_prefix_inv
      (sets : num # (int -> ct_color list set))
      (count : num # (int -> int))
      (n : int) <=>
    (!c : ct_color list.
       (0 : int) <= &(LENGTH c) /\ &(LENGTH c) < n ==>
       ct_valid c ==>
       c IN ct_get sets (&(LENGTH c))) /\
    (!c : ct_color list.
     !i : int.
       (0 : int) <= i /\ i < n ==>
       c IN ct_get sets i ==>
       &(LENGTH c) = i /\ ct_valid c) /\
    (!i : int.
       (0 : int) <= i /\ i < n ==>
       ct_get count i = &(CARD (ct_get sets i)))`;

val ct_inner_inv_def = Define `
  ct_inner_inv
      (sets : num # (int -> ct_color list set))
      (count : num # (int -> int))
      (n : int)
      (k : int) <=>
    ct_prefix_inv sets count n /\
    (!c : ct_color list.
       (c IN ct_get sets n <=>
        &(LENGTH c) = n /\
        ct_valid c /\
        ct_first_black_tile c < k)) /\
    ct_get count n = &(CARD (ct_get sets n))`;

val ct_post_def = Define `
  ct_post
      (sets : num # (int -> ct_color list set))
      (count : num # (int -> int)) <=>
    ct_alen count = (51 : int) /\
    (51 : int) = ct_alen sets /\
    (!i : int.
       (0 : int) <= i /\ i <= 50 ==>
       (!c : ct_color list.
          &(LENGTH c) = i ==>
          (ct_valid c <=> c IN ct_get sets i))) /\
    (!i : int.
       (0 : int) <= i /\ i < 50 ==>
       ct_get count i = &(CARD (ct_get sets i)))`;

val ct_inner_step_def = Define `
  ct_inner_step
      (sets : num # (int -> ct_color list set))
      (count : num # (int -> int))
      (n : int)
      (k : int) <=>
    let o10 = n - k - 1 in
      ct_in_bounds count o10 /\
      ct_in_bounds count n /\
      let o11 = ct_get count n + ct_get count o10 in
        ct_in_bounds count n /\
        (ct_update_ok count n o11 ==>
         let count1 = ct_set count n o11 in
         let o12 = n - k - 1 in
           ct_in_bounds sets o12 /\
           let ns = ct_mapaddleft (ct_get sets o12) k in
             ct_in_bounds sets n /\
             let o13 = ct_get sets n in
               (!x : ct_color list.
                  x IN o13 ==> ~(x IN ns)) /\
               let o14 = o13 UNION ns in
                 &(CARD o14) =
                   &(CARD o13) + &(CARD ns) ==>
                 ct_in_bounds sets n /\
                 (ct_update_ok sets n o14 ==>
                  ct_inner_inv
                    (ct_set sets n o14)
                    count1 n (k + 1)))`;

val ct_last_add_def = Define `
  ct_last_add
      (sets : num # (int -> ct_color list set))
      (count : num # (int -> int))
      (n : int) <=>
    (0 : int) <= n /\
    let r = ct_red_seq n in
      &(LENGTH r) = n /\
      (!i : int.
         (0 : int) <= i /\ i < n ==>
         ct_color_get r i = CTRed) ==>
      let sr = {r} in
        ct_in_bounds count n /\
        let o11 = ct_get count n + 1 in
          ct_in_bounds count n /\
          (ct_update_ok count n o11 ==>
           let count1 = ct_set count n o11 in
             ct_in_bounds sets n /\
             let o12 = ct_get sets n in
               (!x : ct_color list.
                  x IN o12 ==> ~(x IN sr)) /\
               let o13 = o12 UNION sr in
                 &(CARD o13) =
                   &(CARD o12) + &(CARD sr) ==>
                 ct_in_bounds sets n /\
                 (ct_update_ok sets n o13 ==>
                  ct_prefix_inv
                    (ct_set sets n o13)
                    count1 (n + 1)))`;

val ct_outer_body_def = Define `
  ct_outer_body
      (sets : num # (int -> ct_color list set))
      (count : num # (int -> int))
      (n : int) <=>
    let o5 = n - 1 in
      ct_in_bounds count o5 /\
      let o6 = ct_get count o5 in
        ct_in_bounds count n /\
        (ct_update_ok count n o6 ==>
         let count1 = ct_set count n o6 in
         let o7 = n - 1 in
           ct_in_bounds sets o7 /\
           let o8 =
             ct_mapaddleft (ct_get sets o7) (0 : int)
           in
             ct_in_bounds sets n /\
             (ct_update_ok sets n o8 ==>
              let sets1 = ct_set sets n o8 in
              let o9 = n - 1 in
                ((3 : int) <= o9 + 1 ==>
                 ct_inner_inv sets1 count1 n 3 /\
                 (!sets2 count2.
                    ct_finite_array sets2 ==>
                    ct_alen sets2 = ct_alen sets1 ==>
                    ct_alen count2 = ct_alen count1 ==>
                    ((!k : int.
                       ((3 : int) <= k /\ k <= o9) /\
                       ct_inner_inv sets2 count2 n k ==>
                       ct_inner_step sets2 count2 n k) /\
                     (ct_inner_inv
                        sets2 count2 n (o9 + 1) ==>
                      ct_last_add sets2 count2 n))) /\
                (o9 + 1 < (3 : int) ==>
                 ct_last_add sets1 count1 n)))`;

val ct_outer_vc_def = Define `
  ct_outer_vc
      (sets : num # (int -> ct_color list set))
      (count : num # (int -> int)) <=>
    ct_prefix_inv sets count 4 /\
    (!sets1 count1.
       ct_finite_array sets1 ==>
       ct_alen sets1 = ct_alen sets ==>
       ct_alen count1 = ct_alen count ==>
       ((!n : int.
          (((4 : int) <= n /\ n <= 50) /\
           ct_prefix_inv sets1 count1 n) ==>
          ct_outer_body sets1 count1 n) /\
        (ct_prefix_inv sets1 count1 (50 + 1) ==>
         ct_post sets1 count1)))`;

val ct_initialization_vc_def = Define `
  ct_initialization_vc
      (count : num # (int -> int))
      (sets : num # (int -> ct_color list set)) <=>
    ct_in_bounds count 0 /\
    (ct_update_ok count 0 1 ==>
     let count0 = ct_set count 0 1 in
     let o1 = {ct_black_seq 0} in
       ct_in_bounds sets 0 /\
       (ct_update_ok sets 0 o1 ==>
        let sets0 = ct_set sets 0 o1 in
          ct_in_bounds count0 1 /\
          (ct_update_ok count0 1 1 ==>
           let count1 = ct_set count0 1 1 in
           let o2 = {ct_black_seq 1} in
             ct_in_bounds sets0 1 /\
             (ct_update_ok sets0 1 o2 ==>
              let sets1 = ct_set sets0 1 o2 in
                ct_in_bounds count1 2 /\
                (ct_update_ok count1 2 1 ==>
                 let count2 = ct_set count1 2 1 in
                 let o3 = {ct_black_seq 2} in
                   ct_in_bounds sets1 2 /\
                   (ct_update_ok sets1 2 o3 ==>
                    let sets2 = ct_set sets1 2 o3 in
                      ct_in_bounds count2 3 /\
                      (ct_update_ok count2 3 2 ==>
                       let count3 = ct_set count2 3 2 in
                       let o4 =
                         {ct_red_seq 3; ct_black_seq 3}
                       in
                         ct_in_bounds sets2 3 /\
                         (ct_update_ok sets2 3 o4 ==>
                          let sets3 = ct_set sets2 3 o4 in
                            (((4 : int) <= 50 + 1 ==>
                              ct_outer_vc sets3 count3) /\
                             (50 + 1 < (4 : int) ==>
                              ct_post sets3 count3))))))))))`;

val verifythis_2018_le_rouge_et_le_noir_1_ColoredTiles_enumqtvc_statement =
  ``(0 : int) <= 51 /\
    (!count : num # (int -> int).
       ct_array_init count 51 (0 : int) ==>
       (0 : int) <= 51 /\
       (!sets : num # (int -> ct_color list set).
          ct_array_init sets 51 ({} : ct_color list set) ==>
          ct_initialization_vc count sets))``;
