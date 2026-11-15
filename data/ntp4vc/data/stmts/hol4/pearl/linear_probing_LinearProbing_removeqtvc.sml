(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linear_probing_LinearProbing_removeqtvc: the verification condition
  for removing a non-dummy key from a linear-probing hash table while
  preserving its representation invariant and updated abstract view. This
  file contains no proof.
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

val lp_next_def = Define `
  lp_next (n : int) (i : int) =
    let i1 = i + 1
    in
      if i1 = n then 0 else i1`;

val linear_probing_LinearProbing_remove_vc =
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
        let o1 = data h
        in
          (~(keym1 x = keym1 dummy) /\
           (let n = &(LENGTH o1)
            in
              0 < n /\
              0 < lp_numof keym1 dummy o1 0 n)) /\
          (!j : int.
             (0 <= j /\ j < &(LENGTH o1)) /\
             (keym1 (lp_get o1 j) = keym1 dummy \/
              keym1 (lp_get o1 j) = keym1 x) /\
             (!j1 : int.
                0 <= j1 /\ j1 < &(LENGTH o1) ==>
                lp_between
                  (lp_bucket hash x (&(LENGTH o1))) j1 j ==>
                ~(keym1 (lp_get o1 j1) = keym1 x) /\
                ~(keym1 (lp_get o1 j1) = keym1 dummy)) ==>
             let o2 = dummy
             in
             let o3 = data h
             in
               (0 <= j /\ j < &(LENGTH o3)) /\
               (let o4 = lp_get o3 j
                in
                  (~(keym1 o4 = keym1 o2) <=>
                   ~(keym1 o4 = keym1 o2)) ==>
                  if ~(keym1 o4 = keym1 o2) then
                    let o5 = dummy
                    in
                    let o6 = data h
                    in
                      (0 <= j /\ j < &(LENGTH o6)) /\
                      (LENGTH
                         (LUPDATE o5 (lp_to_num j) o6) =
                         LENGTH o6 ==>
                       LENGTH
                         (LUPDATE o5 (lp_to_num j) o6) =
                         LENGTH (data h) ==>
                       (!q : int.
                          0 <= q /\ q < &(LENGTH o6) ==>
                          lp_get
                            (LUPDATE o5 (lp_to_num j) o6) q =
                            lp_fun_update (lp_get o6) j o5 q) ==>
                       let o7 = lp_next (&(LENGTH (data h))) j
                       in
                         (0 <= j /\
                          j <
                            &(LENGTH
                                (LUPDATE o5 (lp_to_num j) o6))) /\
                         (0 <= o7 /\
                          o7 <
                            &(LENGTH
                                (LUPDATE o5 (lp_to_num j) o6))) /\
                         ~(o7 = j) /\
                         (if j <= o7 then
                            1 <=
                              lp_numof keym1 dummy
                                (LUPDATE o5 (lp_to_num j) o6)
                                o7
                                (&(LENGTH
                                    (LUPDATE o5
                                      (lp_to_num j) o6))) +
                              lp_numof keym1 dummy
                                (LUPDATE o5 (lp_to_num j) o6)
                                0 j
                          else
                            1 <=
                              lp_numof keym1 dummy
                                (LUPDATE o5 (lp_to_num j) o6)
                                o7 j) /\
                         (!k : int.
                            0 <= k /\
                            k <
                              &(LENGTH
                                  (LUPDATE o5
                                    (lp_to_num j) o6)) ==>
                            lp_between j k o7 ==>
                            ~(k = j) ==>
                            ~(keym1
                                (lp_get
                                  (LUPDATE o5
                                    (lp_to_num j) o6) k) =
                              keym1 dummy)) /\
                         (!f0 : int.
                            (0 <= f0 /\
                             f0 <
                               &(LENGTH
                                   (LUPDATE o5
                                     (lp_to_num j) o6))) /\
                            ~(f0 = j) /\
                            keym1
                                (lp_get
                                  (LUPDATE o5
                                    (lp_to_num j) o6) f0) =
                              keym1 dummy /\
                            (!k : int.
                               0 <= k /\
                               k <
                                 &(LENGTH
                                     (LUPDATE o5
                                       (lp_to_num j) o6)) ==>
                               lp_between j k f0 ==>
                               ~(k = j) ==>
                               ~(keym1
                                   (lp_get
                                     (LUPDATE o5
                                       (lp_to_num j) o6) k) =
                                 keym1 dummy)) ==>
                            (0 <= f0 /\
                             f0 <
                               &(LENGTH
                                   (LUPDATE o5
                                     (lp_to_num j) o6))) /\
                            (0 <= j /\
                             j <
                               &(LENGTH
                                   (LUPDATE o5
                                     (lp_to_num j) o6))) /\
                            (0 <= j /\
                             j <
                               &(LENGTH
                                   (LUPDATE o5
                                     (lp_to_num j) o6))) /\
                            ~(j = f0) /\
                            keym1
                                (lp_get
                                  (LUPDATE o5
                                    (lp_to_num j) o6) j) =
                              keym1 dummy /\
                            keym1
                                (lp_get
                                  (LUPDATE o5
                                    (lp_to_num j) o6) f0) =
                              keym1 dummy /\
                            lp_between j j f0 /\
                            (!k : int.
                               0 <= k /\
                               k <
                                 &(LENGTH
                                     (LUPDATE o5
                                       (lp_to_num j) o6)) ==>
                               lp_between j k f0 ==>
                               ~(k = j) ==>
                               ~(keym1
                                   (lp_get
                                     (LUPDATE o5
                                       (lp_to_num j) o6) k) =
                                 keym1 dummy)) /\
                            ~(lp_fun_update
                                (view h) (keym1 x) F
                                (keym1 dummy) = T) /\
                            (!k : int.
                               0 <= k /\
                               k <
                                 &(LENGTH
                                     (LUPDATE o5
                                       (lp_to_num j) o6)) ==>
                               let x1 =
                                 lp_get
                                   (LUPDATE o5
                                     (lp_to_num j) o6) k
                               in
                                 ~(keym1 x1 = keym1 dummy) ==>
                                 lp_fun_update
                                     (view h) (keym1 x) F
                                     (keym1 x1) =
                                   T /\
                                 loc h (keym1 x1) = k) /\
                            (let n =
                               &(LENGTH
                                   (LUPDATE o5
                                     (lp_to_num j) o6))
                             in
                               !x1 : 'key.
                                 lp_fun_update
                                     (view h) (keym1 x) F
                                     (keym1 x1) =
                                   T ==>
                                 let k = loc h (keym1 x1)
                                 in
                                   (0 <= k /\ k < n) /\
                                   keym1
                                       (lp_get
                                         (LUPDATE o5
                                           (lp_to_num j) o6) k) =
                                     keym1 x1 /\
                                   (!l : int.
                                      0 <= l /\ l < n ==>
                                      lp_between
                                        (lp_bucket hash x1 n) l k ==>
                                      ~(keym1
                                          (lp_get
                                            (LUPDATE o5
                                              (lp_to_num j) o6) l) =
                                        keym1 x1) /\
                                      (~(keym1
                                           (lp_get
                                             (LUPDATE o5
                                               (lp_to_num j) o6) l) =
                                         keym1 dummy) \/
                                       l = j /\
                                       lp_between j j k))) /\
                            (!l : 'keym -> int.
                             !h_data : 'key list.
                               LENGTH h_data =
                                 LENGTH
                                   (LUPDATE o5
                                     (lp_to_num j) o6) ==>
                               LENGTH h_data =
                                 LENGTH
                                   (LUPDATE o5
                                     (lp_to_num j) o6) ==>
                               (lp_numof keym1 dummy h_data
                                    0 (&(LENGTH h_data)) =
                                  lp_numof keym1 dummy
                                    (LUPDATE o5
                                      (lp_to_num j) o6)
                                    0 (&(LENGTH h_data)) /\
                                lp_valid keym1 hash dummy h_data
                                  (lp_fun_update
                                    (view h) (keym1 x) F) l) ==>
                               !h1 : 'state.
                                 ((0 <= size h - 1 /\
                                   size h - 1 <
                                     &(LENGTH h_data)) /\
                                  (let n = &(LENGTH h_data)
                                   in
                                     size h - 1 +
                                         lp_numof keym1 dummy
                                           h_data 0 n =
                                       n) /\
                                  lp_valid keym1 hash dummy h_data
                                    (lp_fun_update
                                      (view h) (keym1 x) F) l) /\
                                 (l = loc h1 /\
                                  lp_fun_update
                                      (view h) (keym1 x) F =
                                    view h1 /\
                                  h_data = data h1 /\
                                  size h - 1 = size h1 ==>
                                  view h1 =
                                    lp_fun_update
                                      (view h) (keym1 x) F))))
                  else
                    view h =
                      lp_fun_update (view h) (keym1 x) F))``;
