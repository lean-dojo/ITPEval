(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linear_probing_LinearProbing_memqtvc: the verification condition for
  membership probing in a valid linear-probing hash table, relating a reached
  dummy or matching bucket entry to the table's abstract view. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory pred_setTheory;

val lp_to_num_def = Define `
  lp_to_num (z : int) = if z < 0 then 0 else Num z`;

val lp_get_def = Define `
  lp_get (xs : 'a list) (i : int) =
    if lp_to_num i < LENGTH xs then EL (lp_to_num i) xs else ARB`;

val lp_bucket_def = Define `
  lp_bucket (hash : 'key -> int) (k : 'key) (n : int) =
    hash k rem n`;

val lp_between_def = Define `
  lp_between (l : int) (j : int) (r : int) <=>
    l <= j /\ j < r \/
    r < l /\ l <= j \/
    j < r /\ r < l`;

val lp_numof_def = Define `
  lp_numof
    (keym1 : 'key -> 'keym)
    (dummy : 'key)
    (xs : 'key list)
    (l : int)
    (u : int) =
      &(CARD
          {i : int |
             l <= i /\ i < u /\
             keym1 (lp_get xs i) = keym1 dummy})`;

val lp_valid_def = Define `
  lp_valid
    (keym1 : 'key -> 'keym)
    (hash : 'key -> int)
    (dummy : 'key)
    (xs : 'key list)
    (vw : 'keym -> bool)
    (lc : 'keym -> int) <=>
      ~(vw (keym1 dummy) = T) /\
      (!i : int.
         0 <= i /\ i < &(LENGTH xs) ==>
         let x = lp_get xs i
         in
           ~(keym1 x = keym1 dummy) ==>
           vw (keym1 x) = T /\ lc (keym1 x) = i) /\
      (let n = &(LENGTH xs)
       in
         !x : 'key.
           vw (keym1 x) = T ==>
           let i = lc (keym1 x)
           in
             (0 <= i /\ i < n) /\
             keym1 (lp_get xs i) = keym1 x /\
             (!j : int.
                0 <= j /\ j < n ==>
                lp_between (lp_bucket hash x n) j i ==>
                ~(keym1 (lp_get xs j) = keym1 x) /\
                ~(keym1 (lp_get xs j) = keym1 dummy)))`;

val linear_probing_LinearProbing_mem_vc =
  ``!(keym1 : 'key -> 'keym).
    !(hash : 'key -> int).
    !(dummy : 'key).
    !(size : 'state -> int).
    !(data : 'state -> 'key list).
    !(view : 'state -> 'keym -> bool).
    !(loc : 'state -> 'keym -> int).
      (!k : 'key. 0 <= hash k) ==>
      (!x y : 'key.
         keym1 x = keym1 y ==> hash x = hash y) ==>
      (!self : 'state.
         0 <= size self /\
         size self < &(LENGTH (data self)) /\
         size self +
             lp_numof keym1 dummy (data self)
               0 (&(LENGTH (data self))) =
           &(LENGTH (data self)) /\
         lp_valid keym1 hash dummy
           (data self) (view self) (loc self)) ==>
      (!a b : 'state.
         size a = size b /\
         data a = data b /\
         view a = view b /\
         loc a = loc b ==>
         a = b) ==>
      !x : 'key.
      !h : 'state.
        ~(keym1 x = keym1 dummy) ==>
        let o1 = dummy
        in
        let o2 = data h
        in
          (~(keym1 x = keym1 dummy) /\
           (let n = &(LENGTH o2)
            in
              0 < n /\
              0 < lp_numof keym1 dummy o2 0 n)) /\
          (!o3 : int.
             (0 <= o3 /\ o3 < &(LENGTH o2)) /\
             (keym1 (lp_get o2 o3) = keym1 dummy \/
              keym1 (lp_get o2 o3) = keym1 x) /\
             (!j : int.
                0 <= j /\ j < &(LENGTH o2) ==>
                lp_between
                  (lp_bucket hash x (&(LENGTH o2))) j o3 ==>
                ~(keym1 (lp_get o2 j) = keym1 x) /\
                ~(keym1 (lp_get o2 j) = keym1 dummy)) ==>
             let o4 = data h
             in
               (0 <= o3 /\ o3 < &(LENGTH o4)) /\
               (let o5 = lp_get o4 o3
                in
                  (~(keym1 o5 = keym1 o1) <=>
                   ~(keym1 o5 = keym1 o1)) ==>
                  (~(keym1 o5 = keym1 o1) <=>
                   view h (keym1 x) = T)))``;
