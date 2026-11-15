(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binary_search_Complexity_binary_searchqtvc: a binary-search
  verification condition preserving the search invariant and a logarithmic
  running-time bound over a sorted integer list. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory;

val binary_search_complexity_vc =
  ``let vc_to_nat =
      \z : int. if z < 0 then 0 else Num z
    in
    let vc_get =
      \xs : int list. \z : int.
        if vc_to_nat z < LENGTH xs then EL (vc_to_nat z) xs else 0
    in
      !log2 : int -> int.
        (!n : int.
           if n <= 1 then
             log2 n = 0
           else
             log2 n = 1 + log2 (n quot 2)) ==>
        let f =
          \n : int. if n = 0 then 0 else 1 + log2 n
        in
          !a : int list.
          !v : int.
            (!i1 i2 : int.
               0 <= i1 /\ i1 <= i2 /\ i2 < &(LENGTH a) ==>
               vc_get a i1 <= vc_get a i2) ==>
            let o1 = &(LENGTH a) in
              ((0 <= (0 : int) /\ 0 <= o1 /\ o1 <= &(LENGTH a)) /\
               (!i : int.
                  (0 <= i /\ i < 0 \/
                   o1 <= i /\ i < &(LENGTH a)) ==>
                  ~(vc_get a i = v)) /\
               0 - 0 + f (o1 - 0) <= f (&(LENGTH a))) /\
              (!hi lo time : int.
                 (0 <= lo /\ lo <= hi /\ hi <= &(LENGTH a)) /\
                 (!i : int.
                    (0 <= i /\ i < lo \/
                     hi <= i /\ i < &(LENGTH a)) ==>
                    ~(vc_get a i = v)) /\
                 time - 0 + f (hi - lo) <= f (&(LENGTH a)) ==>
                 if lo < hi then
                   ~(2 = (0 : int)) /\
                   (let mid = lo + (hi - lo) quot 2 in
                      (0 <= mid /\ mid < &(LENGTH a)) /\
                      if vc_get a mid < v then
                        (0 <= hi - lo /\
                         hi - (mid + 1) < hi - lo) /\
                        (0 <= mid + 1 /\ mid + 1 <= hi /\
                         hi <= &(LENGTH a)) /\
                        (!i : int.
                           (0 <= i /\ i < mid + 1 \/
                            hi <= i /\ i < &(LENGTH a)) ==>
                           ~(vc_get a i = v)) /\
                        time + 1 - 0 + f (hi - (mid + 1)) <=
                          f (&(LENGTH a))
                      else
                        (0 <= mid /\ mid < &(LENGTH a)) /\
                        if v < vc_get a mid then
                          (0 <= hi - lo /\ mid - lo < hi - lo) /\
                          (0 <= lo /\ lo <= mid /\
                           mid <= &(LENGTH a)) /\
                          (!i : int.
                             (0 <= i /\ i < lo \/
                              mid <= i /\ i < &(LENGTH a)) ==>
                             ~(vc_get a i = v)) /\
                          time + 1 - 0 + f (mid - lo) <=
                            f (&(LENGTH a))
                        else
                          (((0 <= mid /\ mid < &(LENGTH a)) /\
                            vc_get a mid = v) \/
                           (mid = ~1 /\
                            !i : int.
                              0 <= i /\ i < &(LENGTH a) ==>
                              ~(vc_get a i = v))) /\
                          time - 0 <= f (&(LENGTH a)))
                 else
                   ((((0 <= (~1 : int) /\ ~1 < &(LENGTH a)) /\
                      vc_get a (~1) = v) \/
                     (!i : int.
                        0 <= i /\ i < &(LENGTH a) ==>
                        ~(vc_get a i = v))) /\
                    time - 0 <= f (&(LENGTH a))))``;
