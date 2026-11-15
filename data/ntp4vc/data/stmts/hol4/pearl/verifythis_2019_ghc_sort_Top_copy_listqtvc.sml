(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_copy_listqtvc: the verification
  condition for copying an integer list into a finite-length, total
  integer-indexed array while preserving copied values, the untouched
  prefix, and occurrence counts. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory pairTheory pred_setTheory;

val verifythis_2019_ghc_sort_Top_copy_list_vc =
  ``let vc_to_num =
      \z : int. if z < 0 then 0 else Num z
    in
    let vc_nth =
      \xs : int list. \z : int.
        if vc_to_num z < LENGTH xs then EL (vc_to_num z) xs else 0
    in
    let vc_length =
      \a : num # (int -> int). &(FST a)
    in
    let vc_get =
      \a : num # (int -> int). \i : int. SND a i
    in
    let vc_update =
      \a : num # (int -> int). \i : int. \value : int.
        (FST a, \j : int. if j = i then value else SND a j)
    in
    let vc_occ =
      \value : int.
       \a : num # (int -> int).
       \lower : int.
       \upper : int.
        CARD
          {i : int |
             lower <= i /\
             i < upper /\
             vc_get a i = value}
    in
    let vc_count =
      \value : int. \xs : int list.
        LENGTH (FILTER (\y : int. y = value) xs)
    in
      !s : int.
      !l : int list.
      !a : num # (int -> int).
        0 <= s ==>
        &(LENGTH l) = vc_length a - s ==>
        case l of
          [] =>
            (!x : int.
               s <= x /\ x < vc_length a ==>
               vc_get a x = vc_nth l (x - s)) /\
            (!x : int.
               vc_occ x a s (vc_length a) =
                 vc_count x l)
        | h::t =>
            (0 <= s /\ s < vc_length a) /\
            (vc_length (vc_update a s h) = vc_length a ==>
             vc_get (vc_update a s h) =
               (\q : int.
                  if q = s then h else vc_get a q) ==>
             let o1 = s + 1
             in
               ((case l of
                   [] => F
                 | _::f => f = t) /\
                0 <= o1 /\
                &(LENGTH t) =
                  vc_length (vc_update a s h) - o1) /\
               (!a1 : num # (int -> int).
                  vc_length a1 =
                    vc_length (vc_update a s h) ==>
                  ((!x : int.
                      o1 <= x /\ x < vc_length a1 ==>
                      vc_get a1 x = vc_nth t (x - o1)) /\
                   (!x : int.
                      0 <= x /\ x < o1 ==>
                      vc_get a1 x =
                        vc_get (vc_update a s h) x) /\
                   (!x : int.
                      vc_occ x a1 o1 (vc_length a1) =
                        vc_count x t)) ==>
                  (!x : int.
                     s <= x /\ x < vc_length a1 ==>
                     vc_get a1 x = vc_nth l (x - s)) /\
                  (!x : int.
                     0 <= x /\ x < s ==>
                     vc_get a1 x = vc_get a x) /\
                  (!x : int.
                     vc_occ x a1 s (vc_length a1) =
                       vc_count x l)))``;
