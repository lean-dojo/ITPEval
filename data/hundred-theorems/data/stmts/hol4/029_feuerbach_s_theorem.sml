(*
  Statement-only formalization of Hundred Theorems item 029, "Feuerbach's Theorem":
  for a nondegenerate real-plane triangle, the circle through the side midpoints and a
  circle tangent to all three side-lines are identical or have exactly one common point.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory transcTheory;

val feuerbachs_theorem =
  ``let collinear =
      \P Q R : real # real.
        (FST P - FST Q) * (SND R - SND Q) =
        (SND P - SND Q) * (FST R - FST Q)
    in
    let midpoint =
      \P Q : real # real.
        ((FST P + FST Q) / 2, (SND P + SND Q) / 2)
    in
    let orthogonal =
      \A B C D : real # real.
        (FST A - FST B) * (FST C - FST D) +
        (SND A - SND B) * (SND C - SND D) = 0
    in
    let dist =
      \P Q : real # real.
        sqrt ((FST P - FST Q) pow 2 + (SND P - SND Q) pow 2)
    in
      !a b c mbc mac mab pbc pac pab ncenter icenter : real # real.
      !nradius iradius : real.
        ~collinear a b c /\
        midpoint a b = mab /\
        midpoint b c = mbc /\
        midpoint c a = mac /\
        dist ncenter mbc = nradius /\
        dist ncenter mac = nradius /\
        dist ncenter mab = nradius /\
        dist icenter pbc = iradius /\
        dist icenter pac = iradius /\
        dist icenter pab = iradius /\
        collinear a b pab /\ orthogonal a b icenter pab /\
        collinear b c pbc /\ orthogonal b c icenter pbc /\
        collinear a c pac /\ orthogonal a c icenter pac
        ==>
        (ncenter = icenter /\ nradius = iradius) \/
        (?!x : real # real.
           dist ncenter x = nradius /\ dist icenter x = iradius)``;
