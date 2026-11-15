(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q536640, "Hall's marriage theorem": a family of finite sets has an
  injective system of representatives exactly when every finite subfamily
  has a union at least as large as its index set. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val hall_s_marriage_theorem =
  ``!(t : 'i -> 'a set).
      (!i. FINITE (t i))
      ==>
      ((!s : 'i set.
          FINITE s ==>
          CARD s <= CARD (BIGUNION (IMAGE t s)))
       <=>
       ?f : 'i -> 'a.
         (!x y. f x = f y ==> x = y) /\
         !x. f x IN t x)``;
