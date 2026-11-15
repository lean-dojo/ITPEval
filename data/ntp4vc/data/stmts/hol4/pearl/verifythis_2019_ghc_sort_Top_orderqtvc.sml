(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_orderqtvc: ordering a monotonic integer
  list by retaining a strictly increasing list or reversing a nonincreasing
  list, yielding a nondecreasing permutation. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val verifythis_2019_ghc_sort_Top_order_vc =
  ``let vc_strict_increasing =
      \xs : int list. SORTED (\x y : int. x < y) xs
    in
    let vc_nondecreasing =
      \xs : int list. SORTED (\x y : int. x <= y) xs
    in
    let vc_nonincreasing =
      \xs : int list. SORTED (\x y : int. y <= x) xs
    in
      !l : int list.
        vc_strict_increasing l \/ vc_nonincreasing l ==>
        (case l of
           [] => T
         | h1::rest =>
             case rest of
               [] => T
             | h2::tail => T) /\
        (!result : int list.
           (case l of
              [] => result = l
            | h1::rest =>
                case rest of
                  [] => result = l
                | h2::tail =>
                    if h1 < h2 then
                      result = l
                    else
                      result = REVERSE l) ==>
           vc_nondecreasing result /\ PERM l result)``;
