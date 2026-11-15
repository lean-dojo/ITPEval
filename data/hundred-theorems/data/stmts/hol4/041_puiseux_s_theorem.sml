(*
  Statement-only formalization of "Puiseux's Theorem" from Hundred Theorems item 041. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pairTheory pred_setTheory ratTheory;

val puiseuxs_theorem =
  ``!(z0 : 'a) (z1 : 'a)
      (plus : 'a -> 'a -> 'a)
      (times : 'a -> 'a -> 'a)
      (negate : 'a -> 'a)
      (reciprocal : 'a -> 'a).
      let field_axioms =
        (z0 <> z1 /\
         (!x. plus z0 x = x) /\
         (!x. plus (negate x) x = z0) /\
         (!x y. plus x y = plus y x) /\
         (!x y z. plus (plus x y) z = plus x (plus y z)) /\
         (!x. times z1 x = x) /\
         (!x y. times x y = times y x) /\
         (!x y z. times (times x y) z = times x (times y z)) /\
         (!x y z.
            times x (plus y z) = plus (times x y) (times x z)) /\
         (!x. x <> z0 ==> times (reciprocal x) x = z1))
      in
      let characteristic_zero =
        !n. 0 < n ==> FOLDL plus z0 (REPLICATE n z1) <> z0
      in
      let base_eval =
        \coeffs x.
          FOLDR (\c acc. plus c (times x acc)) z0 coeffs
      in
      let algebraically_closed =
        !coeffs : 'a list.
          1 < LENGTH coeffs /\ LAST coeffs <> z0 ==>
          ?x : 'a. base_eval coeffs x = z0
      in
      let is_puiseux =
        \(f : rat -> 'a).
          (?lower : rat.
             !q. q < lower ==> f q = z0) /\
          (?denom : num.
             0 < denom /\
             !q. f q <> z0 ==>
                 ?numer : int.
                   q = rat_of_int numer / &denom)
      in
      let coefficient_pairs =
        \(f : rat -> 'a) g q.
          {p |
             f (FST p) <> z0 /\
             g (SND p) <> z0 /\
             q = FST p + SND p}
      in
      let series_zero =
        \q : rat. z0
      in
      let series_add =
        \(f : rat -> 'a) g q. plus (f q) (g q)
      in
      let series_mul =
        \(f : rat -> 'a) g q.
          ITSET
            (\p acc.
               plus (times (f (FST p)) (g (SND p))) acc)
            (coefficient_pairs f g q) z0
      in
      let series_eval =
        \coeffs x.
          FOLDR
            (\c acc. series_add c (series_mul x acc))
            series_zero coeffs
      in
        field_axioms /\
        characteristic_zero /\
        algebraically_closed ==>
        !coeffs : (rat -> 'a) list.
          1 < LENGTH coeffs /\
          EVERY is_puiseux coeffs /\
          LAST coeffs <> series_zero ==>
          ?root : rat -> 'a.
            is_puiseux root /\
            series_eval coeffs root = series_zero``;
