(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linear_probing_LinearProbing_resizeqtvc: the verification condition
  for resizing a linear-probing hash table while preserving its abstract view
  and representation invariant and doubling its backing-array length. This
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

val lp_resize_content_def = Define `
  lp_resize_content
    (keym1 : 'key -> 'keym)
    (hash : 'key -> int)
    (dummy : 'key)
    (data : 'state -> 'key list)
    (view : 'state -> 'keym -> bool)
    (loc : 'state -> 'keym -> int)
    (h : 'state)
    (n2 : int)
    (cutoff : int)
    (xs : 'key list)
    (lc : 'keym -> int) <=>
      lp_numof keym1 dummy xs 0 n2 =
        lp_numof keym1 dummy (data h) 0 cutoff + n2 - cutoff /\
      (!j : int.
         0 <= j /\ j < n2 ==>
         ~(keym1 (lp_get xs j) = keym1 dummy) ==>
         view h (keym1 (lp_get xs j)) = T /\
         lc (keym1 (lp_get xs j)) = j) /\
      (!x : 'key.
         view h (keym1 x) = T ==>
         if loc h (keym1 x) < cutoff then
           let j2 = lc (keym1 x)
           in
             (0 <= j2 /\ j2 < n2) /\
             keym1 (lp_get xs j2) = keym1 x /\
             (!k : int.
                0 <= k /\ k < n2 ==>
                lp_between (lp_bucket hash x n2) k j2 ==>
                ~(keym1 (lp_get xs k) = keym1 x) /\
                ~(keym1 (lp_get xs k) = keym1 dummy))
         else
           !j2 : int.
             0 <= j2 /\ j2 < n2 ==>
             ~(keym1 (lp_get xs j2) = keym1 x))`;

val lp_resize_state_def = Define `
  lp_resize_state
    (keym1 : 'key -> 'keym)
    (hash : 'key -> int)
    (dummy : 'key)
    (size : 'state -> int)
    (view : 'state -> 'keym -> bool)
    (h : 'state)
    (xs : 'key list)
    (lc : 'keym -> int) <=>
      (0 <= size h /\ size h < &(LENGTH xs)) /\
      (let n3 = &(LENGTH xs)
       in size h + lp_numof keym1 dummy xs 0 n3 = n3) /\
      lp_valid keym1 hash dummy xs (view h) lc`;

val lp_resize_place_def = Define `
  lp_resize_place
    (keym1 : 'key -> 'keym)
    (hash : 'key -> int)
    (dummy : 'key)
    (data : 'state -> 'key list)
    (view : 'state -> 'keym -> bool)
    (loc : 'state -> 'keym -> int)
    (h : 'state)
    (n2 : int)
    (i : int)
    (a1 : 'key list)
    (lc : 'keym -> int) <=>
      let o3 = data h
      in
        (0 <= i /\ i < &(LENGTH o3)) /\
        (let x = lp_get o3 i
         in
         let o4 = dummy
         in
           (~(keym1 x = keym1 o4) <=>
            ~(keym1 x = keym1 o4)) ==>
           if ~(keym1 x = keym1 o4) then
             (~(keym1 x = keym1 dummy) /\
              (let n1 = &(LENGTH a1)
               in
                 0 < n1 /\
                 0 < lp_numof keym1 dummy a1 0 n1)) /\
             (!j : int.
                (0 <= j /\ j < &(LENGTH a1)) /\
                (keym1 (lp_get a1 j) = keym1 dummy \/
                 keym1 (lp_get a1 j) = keym1 x) /\
                (!j1 : int.
                   0 <= j1 /\ j1 < &(LENGTH a1) ==>
                   lp_between
                     (lp_bucket hash x (&(LENGTH a1))) j1 j ==>
                   ~(keym1 (lp_get a1 j1) = keym1 x) /\
                   ~(keym1 (lp_get a1 j1) = keym1 dummy)) ==>
                (0 <= j /\ j < &(LENGTH a1)) /\
                (LENGTH (LUPDATE x (lp_to_num j) a1) = LENGTH a1 ==>
                 lp_array_function_equal
                   (LUPDATE x (lp_to_num j) a1)
                   (lp_get (LUPDATE x (lp_to_num j) a1))
                   (lp_fun_update (lp_get a1) j x) ==>
                 lp_resize_content
                   keym1 hash dummy data view loc h n2 (i + 1)
                   (LUPDATE x (lp_to_num j) a1)
                   (lp_fun_update lc (keym1 x) j)))
           else
             lp_resize_content
               keym1 hash dummy data view loc h n2 (i + 1) a1 lc)`;

val linear_probing_LinearProbing_resize_vc =
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
      !h : 'state.
        let n = &(LENGTH (data h))
        in
        let n2 = 2 * n
        in
          0 <= n2 /\
          (!a : 'key list.
             (!i : int.
                0 <= i /\ i < n2 ==>
                lp_get a i = dummy) /\
             &(LENGTH a) = n2 ==>
             let o1 = \q : 'keym. 0
             in
             let o2 = n - 1
             in
               (0 <= o2 + 1 ==>
                lp_resize_content
                  keym1 hash dummy data view loc h n2 0 a o1 /\
                (!l : 'keym -> int.
                 !a1 : 'key list.
                   LENGTH a1 = LENGTH a ==>
                   ((!i : int.
                       (0 <= i /\ i <= o2) /\
                       lp_resize_content
                         keym1 hash dummy data view loc h
                         n2 i a1 l ==>
                       lp_resize_place
                         keym1 hash dummy data view loc h
                         n2 i a1 l) /\
                    (lp_resize_content
                       keym1 hash dummy data view loc h
                       n2 (o2 + 1) a1 l ==>
                     !h1 : 'state.
                       lp_resize_state
                         keym1 hash dummy size view h a1 l /\
                       (l = loc h1 /\
                        view h = view h1 /\
                        a1 = data h1 /\
                        size h = size h1 ==>
                        &(LENGTH (data h1)) =
                          2 * &(LENGTH (data h))))))) /\
               (o2 + 1 < 0 ==>
                !h1 : 'state.
                  lp_resize_state
                    keym1 hash dummy size view h a o1 /\
                  (o1 = loc h1 /\
                   view h = view h1 /\
                   a = data h1 /\
                   size h = size h1 ==>
                   &(LENGTH (data h1)) =
                     2 * &(LENGTH (data h)))))``;
