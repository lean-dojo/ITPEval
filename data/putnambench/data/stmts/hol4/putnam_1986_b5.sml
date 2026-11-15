(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_b5:
  the assertion that every real-polynomial triple preserving
  x^2 + y^2 + z^2 + xyz is an allowed signed coordinate permutation is false.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_sigmaTheory;

val putnam_1986_b5 =
  ``let support =
      \p : num # (num # num) -> real.
        {ijk : num # (num # num) | p ijk <> 0}
    in
    let polynomial =
      \p : num # (num # num) -> real.
        FINITE (support p)
    in
    let eval =
      \p : num # (num # num) -> real.
      \x y z : real.
        REAL_SUM_IMAGE
          (\ijk : num # (num # num).
             p ijk *
             x pow (FST ijk) *
             y pow (FST (SND ijk)) *
             z pow (SND (SND ijk)))
          (support p)
    in
    let xpoly =
      \ijk : num # (num # num).
        if ijk = (1, (0, 0)) then (1 : real) else 0
    in
    let ypoly =
      \ijk : num # (num # num).
        if ijk = (0, (1, 0)) then (1 : real) else 0
    in
    let zpoly =
      \ijk : num # (num # num).
        if ijk = (0, (0, 1)) then (1 : real) else 0
    in
    let negpoly =
      \p : num # (num # num) -> real.
      \ijk : num # (num # num).
        -p ijk
    in
    let f =
      \ijk : num # (num # num).
        if ijk = (2, (0, 0)) \/
           ijk = (0, (2, 0)) \/
           ijk = (0, (0, 2)) \/
           ijk = (1, (1, 1))
        then (1 : real)
        else 0
    in
    let perms =
      {s : (num # (num # num) -> real) set |
         s = {xpoly; ypoly; zpoly} \/
         s = {xpoly; negpoly ypoly; negpoly zpoly} \/
         s = {negpoly xpoly; ypoly; negpoly zpoly} \/
         s = {negpoly xpoly; negpoly ypoly; zpoly}}
    in
    let putnam_1986_b5_solution = F
    in
      ((!p q r : num # (num # num) -> real.
          polynomial p /\
          polynomial q /\
          polynomial r /\
          (!x y z : real.
             eval f x y z =
             eval f (eval p x y z) (eval q x y z) (eval r x y z))
          ==>
          {p; q; r} IN perms)
       <=>
       putnam_1986_b5_solution)``;
