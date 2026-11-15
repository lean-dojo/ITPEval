(*
  Statement-only formalization of the Babel-formal artifact galois: field
  cancellation laws and solvability across polynomial maps and splitting-field
  towers. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_theory "hello";

val add_cancel_l =
  ``!(zerof : 'f) (onef : 'f)
      (addf : 'f -> 'f -> 'f) (mulf : 'f -> 'f -> 'f)
      (oppf : 'f -> 'f) (invf : 'f -> 'f).
      ((!x y. addf x y = addf y x) /\
       (!x y z. addf (addf x y) z = addf x (addf y z)) /\
       (!x. addf x zerof = x) /\
       (!x. addf (oppf x) x = zerof) /\
       (!x y. mulf x y = mulf y x) /\
       (!x y z. mulf (mulf x y) z = mulf x (mulf y z)) /\
       (!x. mulf onef x = x) /\
       (!x. ~(x = zerof) ==> mulf (invf x) x = onef) /\
       (!x y z.
          mulf x (addf y z) = addf (mulf x y) (mulf x z)) /\
       ~(zerof = onef) /\
       (!x. ~(x = zerof) ==> ~(invf x = zerof))) ==>
      !x y z. addf x y = addf x z ==> y = z``;

val add_cancel_r =
  ``!(zerof : 'f) (onef : 'f)
      (addf : 'f -> 'f -> 'f) (mulf : 'f -> 'f -> 'f)
      (oppf : 'f -> 'f) (invf : 'f -> 'f).
      ((!x y. addf x y = addf y x) /\
       (!x y z. addf (addf x y) z = addf x (addf y z)) /\
       (!x. addf x zerof = x) /\
       (!x. addf (oppf x) x = zerof) /\
       (!x y. mulf x y = mulf y x) /\
       (!x y z. mulf (mulf x y) z = mulf x (mulf y z)) /\
       (!x. mulf onef x = x) /\
       (!x. ~(x = zerof) ==> mulf (invf x) x = onef) /\
       (!x y z.
          mulf x (addf y z) = addf (mulf x y) (mulf x z)) /\
       ~(zerof = onef) /\
       (!x. ~(x = zerof) ==> ~(invf x = zerof))) ==>
      !x y z. addf y x = addf z x ==> y = z``;

val mul_cancel_l =
  ``!(zerof : 'f) (onef : 'f)
      (addf : 'f -> 'f -> 'f) (mulf : 'f -> 'f -> 'f)
      (oppf : 'f -> 'f) (invf : 'f -> 'f).
      ((!x y. addf x y = addf y x) /\
       (!x y z. addf (addf x y) z = addf x (addf y z)) /\
       (!x. addf x zerof = x) /\
       (!x. addf (oppf x) x = zerof) /\
       (!x y. mulf x y = mulf y x) /\
       (!x y z. mulf (mulf x y) z = mulf x (mulf y z)) /\
       (!x. mulf onef x = x) /\
       (!x. ~(x = zerof) ==> mulf (invf x) x = onef) /\
       (!x y z.
          mulf x (addf y z) = addf (mulf x y) (mulf x z)) /\
       ~(zerof = onef) /\
       (!x. ~(x = zerof) ==> ~(invf x = zerof))) ==>
      !x y z.
        ~(x = zerof) ==> mulf x y = mulf x z ==> y = z``;

val mul_cancel_r =
  ``!(zerof : 'f) (onef : 'f)
      (addf : 'f -> 'f -> 'f) (mulf : 'f -> 'f -> 'f)
      (oppf : 'f -> 'f) (invf : 'f -> 'f).
      ((!x y. addf x y = addf y x) /\
       (!x y z. addf (addf x y) z = addf x (addf y z)) /\
       (!x. addf x zerof = x) /\
       (!x. addf (oppf x) x = zerof) /\
       (!x y. mulf x y = mulf y x) /\
       (!x y z. mulf (mulf x y) z = mulf x (mulf y z)) /\
       (!x. mulf onef x = x) /\
       (!x. ~(x = zerof) ==> mulf (invf x) x = onef) /\
       (!x y z.
          mulf x (addf y z) = addf (mulf x y) (mulf x z)) /\
       ~(zerof = onef) /\
       (!x. ~(x = zerof) ==> ~(invf x = zerof))) ==>
      !x y z.
        ~(x = zerof) ==> mulf y x = mulf z x ==> y = z``;

val inv_unique =
  ``!(zerof : 'f) (onef : 'f)
      (addf : 'f -> 'f -> 'f) (mulf : 'f -> 'f -> 'f)
      (oppf : 'f -> 'f) (invf : 'f -> 'f).
      ((!x y. addf x y = addf y x) /\
       (!x y z. addf (addf x y) z = addf x (addf y z)) /\
       (!x. addf x zerof = x) /\
       (!x. addf (oppf x) x = zerof) /\
       (!x y. mulf x y = mulf y x) /\
       (!x y z. mulf (mulf x y) z = mulf x (mulf y z)) /\
       (!x. mulf onef x = x) /\
       (!x. ~(x = zerof) ==> mulf (invf x) x = onef) /\
       (!x y z.
          mulf x (addf y z) = addf (mulf x y) (mulf x z)) /\
       ~(zerof = onef) /\
       (!x. ~(x = zerof) ==> ~(invf x = zerof))) ==>
      !x y.
        ~(x = zerof) ==> mulf x y = onef ==> y = invf x``;

val inv_involutive =
  ``!(zerof : 'f) (onef : 'f)
      (addf : 'f -> 'f -> 'f) (mulf : 'f -> 'f -> 'f)
      (oppf : 'f -> 'f) (invf : 'f -> 'f).
      ((!x y. addf x y = addf y x) /\
       (!x y z. addf (addf x y) z = addf x (addf y z)) /\
       (!x. addf x zerof = x) /\
       (!x. addf (oppf x) x = zerof) /\
       (!x y. mulf x y = mulf y x) /\
       (!x y z. mulf (mulf x y) z = mulf x (mulf y z)) /\
       (!x. mulf onef x = x) /\
       (!x. ~(x = zerof) ==> mulf (invf x) x = onef) /\
       (!x y z.
          mulf x (addf y z) = addf (mulf x y) (mulf x z)) /\
       ~(zerof = onef) /\
       (!x. ~(x = zerof) ==> ~(invf x = zerof))) ==>
      !x. ~(x = zerof) ==> invf (invf x) = x``;

val map_poly_comp =
  ``!(mapfk : 'pf -> ('f -> 'k) -> 'pk)
      (mapkl : 'pk -> ('k -> 'l) -> 'pl)
      (mapfl : 'pf -> ('f -> 'l) -> 'pl)
      (p : 'pf) (f : 'f -> 'k) (g : 'k -> 'l).
      mapkl (mapfk p f) g = mapfl p (\x. g (f x))``;

val isSolvable_of_isScalarTower =
  ``!(solvf : 'pf -> bool) (solvk : 'pk -> bool)
      (mapfk : 'pf -> ('f -> 'k) -> 'pk)
      (algebrafk : 'f -> 'k) (p : 'pf) q.
      solvf p ==>
      solvk (mapfk q algebrafk) ==>
      solvf q``;

val isSolvable_map_poly =
  ``!(solvf : 'pf -> bool) (solvk : 'pk -> bool)
      (mapfk : 'pf -> ('f -> 'k) -> 'pk)
      (algebrafk : 'f -> 'k) (p : 'pf).
      solvf p ==> solvk (mapfk p algebrafk)``;

val isSolvable_of_splits =
  ``!(solvf : 'pf -> bool)
      (splitsfk : 'pf -> ('f -> 'k) -> bool)
      (p : 'pf) (f : 'f -> 'k).
      splitsfk p f ==> solvf p``;

val gal_isSolvable_tower =
  ``!(solvf : 'p -> bool) (solvfp : 'pp -> bool)
      (mapfp : 'p -> ('f -> 'fp) -> 'pp)
      (splitmapfp : 'p -> 'f -> 'fp) (p : 'p) q.
      (!u v.
         solvf u ==>
         solvfp (mapfp v (splitmapfp p)) ==>
         solvf v) ==>
      solvf p ==>
      solvfp (mapfp q (splitmapfp p)) ==>
      solvf q``;

val gal_isSolvable_double_tower =
  ``!(solvf : 'p -> bool)
      (solvfp : 'pp -> bool) (solvfq : 'pq -> bool)
      (mapfp : 'p -> ('f -> 'fp) -> 'pp)
      (mapfq : 'p -> ('f -> 'fq) -> 'pq)
      (splitmapfp : 'p -> 'f -> 'fp)
      (splitmapfq : 'p -> 'f -> 'fq)
      (p : 'p) q r.
      ((!u v.
          solvf u ==>
          solvfp (mapfp v (splitmapfp p)) ==>
          solvf v) /\
       (!u v.
          solvf u ==>
          solvfq (mapfq v (splitmapfq q)) ==>
          solvf v)) ==>
      solvf p ==>
      solvfp (mapfp q (splitmapfp p)) ==>
      solvfq (mapfq r (splitmapfq q)) ==>
      solvf r``;

val gal_isSolvable_triple_tower =
  ``!(solvf : 'p -> bool)
      (solvfp : 'pp -> bool) (solvfq : 'pq -> bool)
      (solvfr : 'pr -> bool)
      (mapfp : 'p -> ('f -> 'fp) -> 'pp)
      (mapfq : 'p -> ('f -> 'fq) -> 'pq)
      (mapfr : 'p -> ('f -> 'fr) -> 'pr)
      (splitmapfp : 'p -> 'f -> 'fp)
      (splitmapfq : 'p -> 'f -> 'fq)
      (splitmapfr : 'p -> 'f -> 'fr) (p : 'p) q r s.
      ((!u v.
          solvf u ==>
          solvfp (mapfp v (splitmapfp p)) ==>
          solvf v) /\
       (!u v.
          solvf u ==>
          solvfq (mapfq v (splitmapfq q)) ==>
          solvf v) /\
       (!u v.
          solvf u ==>
          solvfr (mapfr v (splitmapfr r)) ==>
          solvf v)) ==>
      solvf p ==>
      solvfp (mapfp q (splitmapfp p)) ==>
      solvfq (mapfq r (splitmapfq q)) ==>
      solvfr (mapfr s (splitmapfr r)) ==>
      solvf s``;

val gal_isSolvable_quadruple_tower =
  ``!(solvf : 'p -> bool)
      (solvfp : 'pp -> bool) (solvfq : 'pq -> bool)
      (solvfr : 'pr -> bool) (solvfs : 'ps -> bool)
      (mapfp : 'p -> ('f -> 'fp) -> 'pp)
      (mapfq : 'p -> ('f -> 'fq) -> 'pq)
      (mapfr : 'p -> ('f -> 'fr) -> 'pr)
      (mapfs : 'p -> ('f -> 'fs) -> 'ps)
      (splitmapfp : 'p -> 'f -> 'fp)
      (splitmapfq : 'p -> 'f -> 'fq)
      (splitmapfr : 'p -> 'f -> 'fr)
      (splitmapfs : 'p -> 'f -> 'fs)
      (p : 'p) q r s t.
      ((!u v.
          solvf u ==>
          solvfp (mapfp v (splitmapfp p)) ==>
          solvf v) /\
       (!u v.
          solvf u ==>
          solvfq (mapfq v (splitmapfq q)) ==>
          solvf v) /\
       (!u v.
          solvf u ==>
          solvfr (mapfr v (splitmapfr r)) ==>
          solvf v) /\
       (!u v.
          solvf u ==>
          solvfs (mapfs v (splitmapfs s)) ==>
          solvf v)) ==>
      solvf p ==>
      solvfp (mapfp q (splitmapfp p)) ==>
      solvfq (mapfq r (splitmapfq q)) ==>
      solvfr (mapfr s (splitmapfr r)) ==>
      solvfs (mapfs t (splitmapfs s)) ==>
      solvf t``;

val gal_isSolvable_map_poly =
  ``!(solvf : 'pf -> bool) (solvk : 'pk -> bool)
      (mapfk : 'pf -> ('f -> 'k) -> 'pk)
      (algebrafk : 'f -> 'k) (p : 'pf).
      (!u. solvf u ==> solvk (mapfk u algebrafk)) ==>
      solvf p ==>
      solvk (mapfk p algebrafk)``;

val gal_isSolvable_of_split =
  ``!(solvf : 'p -> bool)
      (splitsfp : 'p -> ('f -> 'fp) -> bool)
      (splitmapfp : 'p -> 'f -> 'fp) (p : 'p).
      (!u f. splitsfp u f ==> solvf u) ==>
      splitsfp p (splitmapfp p) ==>
      solvf p``;

val gal_isSolvable_split_tower =
  ``!(solvf : 'p -> bool)
      (splitsfp : 'p -> ('f -> 'fp) -> bool)
      (splitmapfp : 'p -> 'f -> 'fp) (p : 'p) q.
      (!u f. splitsfp u f ==> solvf u) ==>
      splitsfp q (splitmapfp p) ==>
      solvf q``;

val gal_isSolvable_two_step_map =
  ``!(solvf : 'pf -> bool) (solvk : 'pk -> bool)
      (solvl : 'pl -> bool)
      (mapfk : 'pf -> ('f -> 'k) -> 'pk)
      (mapkl : 'pk -> ('k -> 'l) -> 'pl)
      (algebrafk : 'f -> 'k) (algebrakl : 'k -> 'l)
      (p : 'pf).
      ((!u. solvf u ==> solvk (mapfk u algebrafk)) /\
       (!v. solvk v ==> solvl (mapkl v algebrakl))) ==>
      solvf p ==>
      solvl (mapkl (mapfk p algebrafk) algebrakl)``;

val gal_isSolvable_three_step_map =
  ``!(solvf : 'pf -> bool) (solvk : 'pk -> bool)
      (solvl : 'pl -> bool) (solvm : 'pm -> bool)
      (mapfk : 'pf -> ('f -> 'k) -> 'pk)
      (mapkl : 'pk -> ('k -> 'l) -> 'pl)
      (maplm : 'pl -> ('l -> 'm) -> 'pm)
      (algebrafk : 'f -> 'k) (algebrakl : 'k -> 'l)
      (algebralm : 'l -> 'm) (p : 'pf).
      ((!u. solvf u ==> solvk (mapfk u algebrafk)) /\
       (!v. solvk v ==> solvl (mapkl v algebrakl)) /\
       (!w. solvl w ==> solvm (maplm w algebralm))) ==>
      solvf p ==>
      solvm
        (maplm
          (mapkl (mapfk p algebrafk) algebrakl)
          algebralm)``;

val gal_isSolvable_map_poly_comp =
  ``!(solvf : 'pf -> bool) (solvk : 'pk -> bool)
      (solvl : 'pl -> bool)
      (mapfk : 'pf -> ('f -> 'k) -> 'pk)
      (mapkl : 'pk -> ('k -> 'l) -> 'pl)
      (algebrafk : 'f -> 'k) (algebrakl : 'k -> 'l)
      (p : 'pf).
      ((!u. solvf u ==> solvk (mapfk u algebrafk)) /\
       (!v. solvk v ==> solvl (mapkl v algebrakl))) ==>
      solvf p ==>
      solvl (mapkl (mapfk p algebrafk) algebrakl)``;

val gal_isSolvable_mutual_split =
  ``!(solvf : 'p -> bool)
      (splitsfp : 'p -> ('f -> 'fp) -> bool)
      (splitsfq : 'p -> ('f -> 'fq) -> bool)
      (splitmapfp : 'p -> 'f -> 'fp)
      (splitmapfq : 'p -> 'f -> 'fq)
      (p : 'p) q.
      ((!u f. splitsfp u f ==> solvf u) /\
       (!u f. splitsfq u f ==> solvf u)) ==>
      splitsfq p (splitmapfq q) ==>
      splitsfp q (splitmapfp p) ==>
      solvf p /\ solvf q``;

val gal_isSolvable_tower_split =
  ``!(solvf : 'p -> bool) (solvfq : 'pq -> bool)
      (mapfq : 'p -> ('f -> 'fq) -> 'pq)
      (splitsfp : 'p -> ('f -> 'fp) -> bool)
      (splitmapfp : 'p -> 'f -> 'fp)
      (splitmapfq : 'p -> 'f -> 'fq)
      (p : 'p) q r.
      ((!u f. splitsfp u f ==> solvf u) /\
       (!u v.
          solvf u ==>
          solvfq (mapfq v (splitmapfq q)) ==>
          solvf v)) ==>
      splitsfp q (splitmapfp p) ==>
      solvfq (mapfq r (splitmapfq q)) ==>
      solvf r``;

val gal_isSolvable_map_after_split =
  ``!(solvf : 'pf -> bool) (solvk : 'pk -> bool)
      (mapfk : 'pf -> ('f -> 'k) -> 'pk)
      (splitsfp : 'pf -> ('f -> 'fp) -> bool)
      (algebrafk : 'f -> 'k)
      (splitmapfp : 'pf -> 'f -> 'fp)
      (p : 'pf).
      ((!u f. splitsfp u f ==> solvf u) /\
       (!u. solvf u ==> solvk (mapfk u algebrafk))) ==>
      splitsfp p (splitmapfp p) ==>
      solvk (mapfk p algebrafk)``;

val _ = export_theory();
