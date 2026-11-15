(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linear_probing_LinearProbing_addqtvc: the verification condition for
  adding a non-dummy key to a linear-probing hash table while preserving its
  representation invariant and updated abstract view. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory pred_setTheory;

val lp_to_num_def = Define `
  lp_to_num (z : int) = if z < 0 then 0 else Num z`;

val lp_get_def = Define `
  lp_get (xs : 'a list) (i : int) =
    if lp_to_num i < LENGTH xs then EL (lp_to_num i) xs else ARB`;

val lp_fun_update_def = Define `
  lp_fun_update (f : 'a -> 'b) (k : 'a) (v : 'b) =
    \q. if q = k then v else f q`;

val lp_array_function_equal_def = Define `
  lp_array_function_equal
    (xs : 'a list) (f : int -> 'b) (g : int -> 'b) <=>
    !q. 0 <= q /\ q < &(LENGTH xs) ==> f q = g q`;

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

val linear_probing_LinearProbing_add_vc =
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
        (if &(LENGTH (data h)) <= 2 * (size h + 1) then
           !h1 : 'state.
             view h = view h1 /\ size h = size h1 ==>
             &(LENGTH (data h1)) = 2 * &(LENGTH (data h)) ==>
             size h1 + 1 < &(LENGTH (data h1))
         else
           size h + 1 < &(LENGTH (data h))) /\
        (!h1 : 'state.
           view h = view h1 /\ size h = size h1 ==>
           size h1 + 1 < &(LENGTH (data h1)) ==>
           let o1 = data h1
           in
             (~(keym1 x = keym1 dummy) /\
              (let n = &(LENGTH o1)
               in
                 0 < n /\
                 0 < lp_numof keym1 dummy o1 0 n)) /\
             (!i : int.
                (0 <= i /\ i < &(LENGTH o1)) /\
                (keym1 (lp_get o1 i) = keym1 dummy \/
                 keym1 (lp_get o1 i) = keym1 x) /\
                (!j : int.
                   0 <= j /\ j < &(LENGTH o1) ==>
                   lp_between
                     (lp_bucket hash x (&(LENGTH o1))) j i ==>
                   ~(keym1 (lp_get o1 j) = keym1 x) /\
                   ~(keym1 (lp_get o1 j) = keym1 dummy)) ==>
                let o2 = dummy
                in
                let o3 = data h1
                in
                  (0 <= i /\ i < &(LENGTH o3)) /\
                  (let o4 = lp_get o3 i
                   in
                     (keym1 o4 = keym1 o2 <=>
                      keym1 o4 = keym1 o2) ==>
                     if keym1 o4 = keym1 o2 then
                       (0 <= i /\ i < &(LENGTH (data h1))) /\
                       (LENGTH
                          (LUPDATE x (lp_to_num i) (data h1)) =
                          LENGTH (data h1) ==>
                        LENGTH
                          (LUPDATE x (lp_to_num i) (data h1)) =
                          LENGTH (data h1) ==>
                        lp_array_function_equal
                          (LUPDATE x (lp_to_num i) (data h1))
                          (lp_get
                            (LUPDATE x (lp_to_num i) (data h1)))
                          (lp_fun_update (lp_get (data h1)) i x) ==>
                        !h2 : 'state.
                          ((0 <= size h1 + 1 /\
                            size h1 + 1 <
                              &(LENGTH
                                  (LUPDATE x (lp_to_num i)
                                    (data h1)))) /\
                           (let n =
                              &(LENGTH
                                  (LUPDATE x (lp_to_num i)
                                    (data h1)))
                            in
                              size h1 + 1 +
                                  lp_numof keym1 dummy
                                    (LUPDATE x (lp_to_num i)
                                      (data h1))
                                    0 n =
                                n) /\
                           lp_valid keym1 hash dummy
                             (LUPDATE x (lp_to_num i) (data h1))
                             (lp_fun_update
                               (view h1) (keym1 x) T)
                             (lp_fun_update
                               (loc h1) (keym1 x) i)) /\
                          (lp_fun_update
                               (loc h1) (keym1 x) i =
                             loc h2 /\
                           lp_fun_update
                               (view h1) (keym1 x) T =
                             view h2 /\
                           LUPDATE x (lp_to_num i) (data h1) =
                             data h2 /\
                           size h1 + 1 = size h2 ==>
                           view h2 =
                             lp_fun_update
                               (view h) (keym1 x) T))
                     else
                       !h2 : 'state.
                         ((0 <= size h1 /\
                           size h1 < &(LENGTH (data h1))) /\
                          (let n = &(LENGTH (data h1))
                           in
                             size h1 +
                                 lp_numof keym1 dummy
                                   (data h1) 0 n =
                               n) /\
                          lp_valid keym1 hash dummy
                            (data h1)
                            (lp_fun_update
                              (view h1) (keym1 x) T)
                            (lp_fun_update
                              (loc h1) (keym1 x) i)) /\
                         (lp_fun_update
                              (loc h1) (keym1 x) i =
                            loc h2 /\
                          lp_fun_update
                              (view h1) (keym1 x) T =
                            view h2 /\
                          data h1 = data h2 /\
                          size h1 = size h2 ==>
                          view h2 =
                            lp_fun_update
                              (view h) (keym1 x) T))))``;
