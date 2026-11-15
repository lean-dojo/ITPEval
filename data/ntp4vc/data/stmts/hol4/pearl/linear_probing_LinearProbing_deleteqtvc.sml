(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linear_probing_LinearProbing_deleteqtvc: the verification condition
  for deletion and key relocation in a linear-probing hash table while
  preserving its representation invariant. This file contains no proof.
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

val lp_delete_array_function_equal_def = Define `
  lp_delete_array_function_equal
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

val lp_next_def = Define `
  lp_next (n : int) (i : int) =
    let i1 = i + 1
    in
      if i1 = n then 0 else i1`;

val linear_probing_LinearProbing_delete_vc =
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
      !f0 : int.
      !a : 'key list.
      !j i : int.
      !view1 : 'keym -> bool.
      !loc1 : 'keym -> int.
        0 <= f0 ==>
        f0 < &(LENGTH a) ==>
        0 <= j ==>
        j < &(LENGTH a) ==>
        0 <= i ==>
        i < &(LENGTH a) ==>
        ~(j = f0) ==>
        keym1 (lp_get a j) = keym1 dummy ==>
        keym1 (lp_get a f0) = keym1 dummy ==>
        lp_between j i f0 ==>
        (!k : int.
           0 <= k /\ k < &(LENGTH a) ==>
           lp_between i k f0 ==>
           ~(k = i) ==>
           ~(keym1 (lp_get a k) = keym1 dummy)) ==>
        ~(view1 (keym1 dummy) = T) ==>
        (!k : int.
           0 <= k /\ k < &(LENGTH a) ==>
           let x = lp_get a k
           in
             ~(keym1 x = keym1 dummy) ==>
             view1 (keym1 x) = T /\ loc1 (keym1 x) = k) ==>
        (let n = &(LENGTH a)
         in
           !x : 'key.
             view1 (keym1 x) = T ==>
             let k = loc1 (keym1 x)
             in
               (0 <= k /\ k < n) /\
               keym1 (lp_get a k) = keym1 x /\
               (!l : int.
                  0 <= l /\ l < n ==>
                  lp_between (lp_bucket hash x n) l k ==>
                  ~(keym1 (lp_get a l) = keym1 x) /\
                  (~(keym1 (lp_get a l) = keym1 dummy) \/
                   l = j /\ lp_between j i k))) ==>
        let n = &(LENGTH a)
        in
        let i1 = lp_next n i
        in
          (0 <= i1 /\ i1 < &(LENGTH a)) /\
          (let xi = lp_get a i1
           in
           let o1 = dummy
           in
             (~(keym1 xi = keym1 o1) <=>
              ~(keym1 xi = keym1 o1)) ==>
             if ~(keym1 xi = keym1 o1) then
               0 < n /\
               (let r = lp_bucket hash xi n
                in
                  0 <= r /\ r < n ==>
                  !o2 : bool.
                    (if j < r then
                       o2 = (if r <= i1 then T else F)
                     else
                       o2 = F) ==>
                    !o3 : bool.
                      (if o2 = T then
                         o3 = T
                       else
                         ?o4 : bool.
                           (if i1 < j then
                              o4 = (if j < r then T else F)
                            else
                              o4 = F) /\
                           (if o4 = T then
                              o3 = T
                            else if r <= i1 then
                              o3 = (if i1 < j then T else F)
                            else
                              o3 = F)) ==>
                      if o3 = T then
                        (0 <=
                           (if f0 <= i then
                              &(LENGTH a) - i + f0
                            else
                              f0 - i) /\
                         (if f0 <= i1 then
                            &(LENGTH a) - i1 + f0
                          else
                            f0 - i1) <
                         (if f0 <= i then
                            &(LENGTH a) - i + f0
                          else
                            f0 - i)) /\
                        (0 <= f0 /\ f0 < &(LENGTH a)) /\
                        (0 <= j /\ j < &(LENGTH a)) /\
                        (0 <= i1 /\ i1 < &(LENGTH a)) /\
                        ~(j = f0) /\
                        keym1 (lp_get a j) = keym1 dummy /\
                        keym1 (lp_get a f0) = keym1 dummy /\
                        lp_between j i1 f0 /\
                        (!k : int.
                           0 <= k /\ k < &(LENGTH a) ==>
                           lp_between i1 k f0 ==>
                           ~(k = i1) ==>
                           ~(keym1 (lp_get a k) =
                             keym1 dummy)) /\
                        ~(view1 (keym1 dummy) = T) /\
                        (!k : int.
                           0 <= k /\ k < &(LENGTH a) ==>
                           let x = lp_get a k
                           in
                             ~(keym1 x = keym1 dummy) ==>
                             view1 (keym1 x) = T /\
                             loc1 (keym1 x) = k) /\
                        (let n1 = &(LENGTH a)
                         in
                           !x : 'key.
                             view1 (keym1 x) = T ==>
                             let k = loc1 (keym1 x)
                             in
                               (0 <= k /\ k < n1) /\
                               keym1 (lp_get a k) = keym1 x /\
                               (!l : int.
                                  0 <= l /\ l < n1 ==>
                                  lp_between
                                    (lp_bucket hash x n1) l k ==>
                                  ~(keym1 (lp_get a l) =
                                    keym1 x) /\
                                  (~(keym1 (lp_get a l) =
                                     keym1 dummy) \/
                                   l = j /\
                                   lp_between j i1 k)))
                      else
                        !a1 : 'key list.
                          LENGTH a1 = LENGTH a /\
                          (!i2 : int.
                             0 <= i2 /\ i2 < &(LENGTH a1) ==>
                             lp_get a1 i2 = lp_get a i2) ==>
                          (0 <= j /\ j < &(LENGTH a)) /\
                          (LENGTH
                             (LUPDATE xi (lp_to_num j) a) =
                             LENGTH a ==>
                           lp_delete_array_function_equal
                             (LUPDATE xi (lp_to_num j) a)
                             (lp_get
                               (LUPDATE xi (lp_to_num j) a))
                             (lp_fun_update (lp_get a) j xi) ==>
                           !a2 : 'key list.
                             LENGTH a2 =
                               LENGTH
                                 (LUPDATE xi (lp_to_num j) a) /\
                             (!i2 : int.
                                0 <= i2 /\ i2 < &(LENGTH a2) ==>
                                lp_get a2 i2 =
                                  lp_get
                                    (LUPDATE xi
                                      (lp_to_num j) a) i2) ==>
                             let o4 = dummy
                             in
                               (0 <= i1 /\
                                i1 <
                                  &(LENGTH
                                      (LUPDATE xi
                                        (lp_to_num j) a))) /\
                               (LENGTH
                                  (LUPDATE o4 (lp_to_num i1)
                                    (LUPDATE xi
                                      (lp_to_num j) a)) =
                                  LENGTH
                                  (LUPDATE xi
                                      (lp_to_num j) a) ==>
                                lp_delete_array_function_equal
                                  (LUPDATE o4 (lp_to_num i1)
                                    (LUPDATE xi
                                      (lp_to_num j) a))
                                  (lp_get
                                    (LUPDATE o4 (lp_to_num i1)
                                      (LUPDATE xi
                                        (lp_to_num j) a)))
                                  (lp_fun_update
                                    (lp_get
                                      (LUPDATE xi
                                        (lp_to_num j) a))
                                    i1 o4) ==>
                                (0 <=
                                   (if f0 <= i then
                                      &(LENGTH a) - i + f0
                                    else
                                      f0 - i) /\
                                 (if f0 <= i1 then
                                    &(LENGTH
                                        (LUPDATE o4
                                          (lp_to_num i1)
                                          (LUPDATE xi
                                            (lp_to_num j) a))) -
                                      i1 + f0
                                  else
                                    f0 - i1) <
                                 (if f0 <= i then
                                    &(LENGTH a) - i + f0
                                  else
                                    f0 - i)) /\
                                (0 <= f0 /\
                                 f0 <
                                   &(LENGTH
                                       (LUPDATE o4
                                         (lp_to_num i1)
                                         (LUPDATE xi
                                           (lp_to_num j) a)))) /\
                                (0 <= i1 /\
                                 i1 <
                                   &(LENGTH
                                       (LUPDATE o4
                                         (lp_to_num i1)
                                         (LUPDATE xi
                                           (lp_to_num j) a)))) /\
                                (0 <= i1 /\
                                 i1 <
                                   &(LENGTH
                                       (LUPDATE o4
                                         (lp_to_num i1)
                                         (LUPDATE xi
                                           (lp_to_num j) a)))) /\
                                ~(i1 = f0) /\
                                keym1
                                    (lp_get
                                      (LUPDATE o4
                                        (lp_to_num i1)
                                        (LUPDATE xi
                                          (lp_to_num j) a))
                                      i1) =
                                  keym1 dummy /\
                                keym1
                                    (lp_get
                                      (LUPDATE o4
                                        (lp_to_num i1)
                                        (LUPDATE xi
                                          (lp_to_num j) a))
                                      f0) =
                                  keym1 dummy /\
                                lp_between i1 i1 f0 /\
                                (!k : int.
                                   0 <= k /\
                                   k <
                                     &(LENGTH
                                         (LUPDATE o4
                                           (lp_to_num i1)
                                           (LUPDATE xi
                                             (lp_to_num j) a))) ==>
                                   lp_between i1 k f0 ==>
                                   ~(k = i1) ==>
                                   ~(keym1
                                       (lp_get
                                         (LUPDATE o4
                                           (lp_to_num i1)
                                           (LUPDATE xi
                                             (lp_to_num j) a))
                                         k) =
                                     keym1 dummy)) /\
                                ~(view1 (keym1 dummy) = T) /\
                                (!k : int.
                                   0 <= k /\
                                   k <
                                     &(LENGTH
                                         (LUPDATE o4
                                           (lp_to_num i1)
                                           (LUPDATE xi
                                             (lp_to_num j) a))) ==>
                                   let x =
                                     lp_get
                                       (LUPDATE o4
                                         (lp_to_num i1)
                                         (LUPDATE xi
                                           (lp_to_num j) a))
                                       k
                                   in
                                     ~(keym1 x = keym1 dummy) ==>
                                     view1 (keym1 x) = T /\
                                     lp_fun_update loc1
                                       (keym1 xi) j (keym1 x) =
                                       k) /\
                                (let n1 =
                                   &(LENGTH
                                       (LUPDATE o4
                                         (lp_to_num i1)
                                         (LUPDATE xi
                                           (lp_to_num j) a)))
                                 in
                                   !x : 'key.
                                     view1 (keym1 x) = T ==>
                                     let k =
                                       lp_fun_update loc1
                                         (keym1 xi) j (keym1 x)
                                     in
                                       (0 <= k /\ k < n1) /\
                                       keym1
                                           (lp_get
                                             (LUPDATE o4
                                               (lp_to_num i1)
                                               (LUPDATE xi
                                                 (lp_to_num j) a))
                                             k) =
                                         keym1 x /\
                                       (!l : int.
                                          0 <= l /\ l < n1 ==>
                                          lp_between
                                            (lp_bucket hash x n1)
                                            l k ==>
                                          ~(keym1
                                              (lp_get
                                                (LUPDATE o4
                                                  (lp_to_num i1)
                                                  (LUPDATE xi
                                                    (lp_to_num j)
                                                    a))
                                                l) =
                                            keym1 x) /\
                                          (~(keym1
                                               (lp_get
                                                 (LUPDATE o4
                                                   (lp_to_num i1)
                                                   (LUPDATE xi
                                                     (lp_to_num j)
                                                     a))
                                                 l) =
                                             keym1 dummy) \/
                                           l = i1 /\
                                           lp_between i1 i1 k))) /\
                                (!loc2 : 'keym -> int.
                                 !a3 : 'key list.
                                   LENGTH a3 =
                                     LENGTH
                                       (LUPDATE o4
                                         (lp_to_num i1)
                                         (LUPDATE xi
                                           (lp_to_num j) a)) ==>
                                   (lp_numof keym1 dummy a3
                                      0 (&(LENGTH a3)) =
                                    lp_numof keym1 dummy
                                      (LUPDATE o4
                                        (lp_to_num i1)
                                        (LUPDATE xi
                                          (lp_to_num j) a))
                                      0 (&(LENGTH a3)) /\
                                    lp_valid keym1 hash dummy
                                      a3 view1 loc2) ==>
                                   lp_numof keym1 dummy a3
                                      0 (&(LENGTH a3)) =
                                    lp_numof keym1 dummy a
                                      0 (&(LENGTH a3)) /\
                                   lp_valid keym1 hash dummy
                                     a3 view1 loc2))))
             else
               lp_valid keym1 hash dummy a view1 loc1)``;
