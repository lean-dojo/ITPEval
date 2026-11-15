(*
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2015_dancing_links_DancingLinks_removeqtvc: the dancing-links
  removal verification condition, relating two pointer-array updates to removal
  from a valid circular list. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val dancing_links_to_num_def = Define `
  dancing_links_to_num (z : int) =
    if z < 0 then 0 else Num z`;

val dancing_links_get_def = Define `
  dancing_links_get (xs : int list) (i : int) =
    if 0 <= i /\ dancing_links_to_num i < LENGTH xs then
      EL (dancing_links_to_num i) xs
    else
      0`;

val dancing_links_update_def = Define `
  dancing_links_update
    (xs : int list) (i : int) (value : int) =
      LUPDATE value (dancing_links_to_num i) xs`;

val dancing_links_fun_update_def = Define `
  dancing_links_fun_update
    (f : int -> int) (i : int) (value : int) =
      \j. if j = i then value else f j`;

val dancing_links_valid_in_def = Define `
  dancing_links_valid_in
    (prev : 'state -> int list)
    (next : 'state -> int list)
    (n : 'state -> int)
    (l : 'state)
    (i : int) <=>
      (0 <= i /\ i < n l) /\
      (0 <= dancing_links_get (prev l) i /\
       dancing_links_get (prev l) i < n l) /\
      (0 <= dancing_links_get (next l) i /\
       dancing_links_get (next l) i < n l) /\
      dancing_links_get
        (next l) (dancing_links_get (prev l) i) = i /\
      dancing_links_get
        (prev l) (dancing_links_get (next l) i) = i`;

val dancing_links_valid_out_def = Define `
  dancing_links_valid_out
    (prev : 'state -> int list)
    (next : 'state -> int list)
    (n : 'state -> int)
    (l : 'state)
    (i : int) <=>
      (0 <= i /\ i < n l) /\
      (0 <= dancing_links_get (prev l) i /\
       dancing_links_get (prev l) i < n l) /\
      (0 <= dancing_links_get (next l) i /\
       dancing_links_get (next l) i < n l) /\
      dancing_links_get
        (next l) (dancing_links_get (prev l) i) =
          dancing_links_get (next l) i /\
      dancing_links_get
        (prev l) (dancing_links_get (next l) i) =
          dancing_links_get (prev l) i`;

val dancing_links_is_list_def = Define `
  dancing_links_is_list
    (prev : 'state -> int list)
    (next : 'state -> int list)
    (n : 'state -> int)
    (l : 'state)
    (s : int list) <=>
      !k : int.
        0 <= k /\ k < &(LENGTH s) ==>
        (0 <= dancing_links_get s k /\
         dancing_links_get s k < n l) /\
        dancing_links_get (prev l) (dancing_links_get s k) =
          dancing_links_get s
            (if k = 0 then &(LENGTH s) - 1 else k - 1) /\
        dancing_links_get (next l) (dancing_links_get s k) =
          dancing_links_get s
            (if k = &(LENGTH s) - 1 then 0 else k + 1) /\
        (!k' : int.
           0 <= k' /\ k' < &(LENGTH s) ==>
           ~(k = k') ==>
           ~(dancing_links_get s k = dancing_links_get s k'))`;

val verifythis_2015_dancing_links_DancingLinks_removeqtvc_statement =
  ``!(prev : 'state -> int list)
      (next : 'state -> int list)
      (n : 'state -> int).
      (!self : 'state.
         LENGTH (prev self) = LENGTH (next self) /\
         &(LENGTH (next self)) = n self) ==>
      (!a b : 'state.
         prev a = prev b /\
         next a = next b /\
         n a = n b ==>
         a = b) ==>
      !l : 'state.
      !i : int.
      !s : int list.
        dancing_links_valid_in prev next n l i ==>
        dancing_links_is_list prev next n l (CONS i s) ==>
        let o1 = prev l
        in
          (0 <= i /\ i < &(LENGTH o1)) /\
          (let o2 = dancing_links_get o1 i
           in
           let o3 = next l
           in
             (0 <= i /\ i < &(LENGTH o3)) /\
             (let o4 = dancing_links_get o3 i
              in
              let o5 = prev l
              in
                (0 <= o4 /\ o4 < &(LENGTH o5)) /\
                (LENGTH (dancing_links_update o5 o4 o2) =
                   LENGTH o5 ==>
                 LENGTH (dancing_links_update o5 o4 o2) =
                   LENGTH (prev l) ==>
                 dancing_links_get
                     (dancing_links_update o5 o4 o2) =
                   dancing_links_fun_update
                     (dancing_links_get o5) o4 o2 ==>
                 (0 <= i /\ i < &(LENGTH (next l))) /\
                 (let o6 = dancing_links_get (next l) i
                  in
                    (0 <= i /\
                     i <
                       &(LENGTH
                           (dancing_links_update o5 o4 o2))) /\
                    (let o7 =
                       dancing_links_get
                         (dancing_links_update o5 o4 o2) i
                     in
                       (0 <= o7 /\
                        o7 < &(LENGTH (next l))) /\
                       (!l1 : 'state.
                          LENGTH
                              (dancing_links_update
                                 (next l) o7 o6) =
                            LENGTH (next l) ==>
                          LENGTH
                              (dancing_links_update
                                 (next l) o7 o6) =
                            LENGTH (next l) ==>
                          dancing_links_get
                              (dancing_links_update
                                 (next l) o7 o6) =
                            dancing_links_fun_update
                              (dancing_links_get (next l))
                              o7 o6 ==>
                          (LENGTH
                               (dancing_links_update o5 o4 o2) =
                             LENGTH
                               (dancing_links_update
                                  (next l) o7 o6) /\
                           &(LENGTH
                               (dancing_links_update
                                  (next l) o7 o6)) =
                             n l) /\
                          (n l = n l1 /\
                           dancing_links_update
                               (next l) o7 o6 =
                             next l1 /\
                           dancing_links_update o5 o4 o2 =
                             prev l1 ==>
                           dancing_links_valid_out
                             prev next n l1 i /\
                           dancing_links_is_list
                             prev next n l1 s)))))))``;
