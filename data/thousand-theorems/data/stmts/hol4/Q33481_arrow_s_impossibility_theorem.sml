(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q33481, "Arrow's impossibility theorem": every social welfare function on
  a finite electorate and at least three alternatives that satisfies weak
  Pareto and independence of irrelevant alternatives is a dictatorship.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val q33481_preference_order_def = new_definition (
  "q33481_preference_order_def",
  ``q33481_preference_order (r : 'a -> 'a -> bool) <=>
      (!x. r x x) /\
      (!x y. r x y \/ r y x) /\
      (!x y z. r x y /\ r y z ==> r x z)``);

val q33481_profile_def = new_definition (
  "q33481_profile_def",
  ``q33481_profile
      (V : 'i set) (R : 'i -> 'a -> 'a -> bool) <=>
      !i. i IN V ==> q33481_preference_order (R i)``);

val q33481_same_profile_on_def = new_definition (
  "q33481_same_profile_on_def",
  ``q33481_same_profile_on
      (V : 'i set)
      (R : 'i -> 'a -> 'a -> bool)
      (R' : 'i -> 'a -> 'a -> bool) <=>
      !i. i IN V ==> R i = R' i``);

val q33481_strict_preference_def = new_definition (
  "q33481_strict_preference_def",
  ``q33481_strict_preference
      (r : 'a -> 'a -> bool) (x : 'a) (y : 'a) <=>
      r x y /\ ~r y x``);

val q33481_same_order_def = new_definition (
  "q33481_same_order_def",
  ``q33481_same_order
      (r : 'a -> 'a -> bool) (r' : 'a -> 'a -> bool)
      (x : 'a) (y : 'a) <=>
      (q33481_strict_preference r x y <=>
       q33481_strict_preference r' x y) /\
      (q33481_strict_preference r y x <=>
       q33481_strict_preference r' y x)``);

val q33481_social_welfare_def = new_definition (
  "q33481_social_welfare_def",
  ``q33481_social_welfare
      (f : ('i -> 'a -> 'a -> bool) -> 'a -> 'a -> bool)
      (V : 'i set) <=>
      (!R. q33481_profile V R ==>
           q33481_preference_order (f R)) /\
      (!R R'.
         q33481_profile V R /\
         q33481_profile V R' /\
         q33481_same_profile_on V R R'
         ==>
         f R = f R')``);

val q33481_weak_pareto_def = new_definition (
  "q33481_weak_pareto_def",
  ``q33481_weak_pareto
      (f : ('i -> 'a -> 'a -> bool) -> 'a -> 'a -> bool)
      (V : 'i set) (X : 'a set) <=>
      !x y R.
        x IN X /\
        y IN X /\
        q33481_profile V R /\
        (!i. i IN V ==> q33481_strict_preference (R i) x y)
        ==>
        q33481_strict_preference (f R) x y``);

val q33481_ind_of_irr_alts_def = new_definition (
  "q33481_ind_of_irr_alts_def",
  ``q33481_ind_of_irr_alts
      (f : ('i -> 'a -> 'a -> bool) -> 'a -> 'a -> bool)
      (V : 'i set) (X : 'a set) <=>
      !R R' x y.
        q33481_profile V R /\
        q33481_profile V R' /\
        x IN X /\
        y IN X /\
        (!i. i IN V ==> q33481_same_order (R i) (R' i) x y)
        ==>
        q33481_same_order (f R) (f R') x y``);

val q33481_is_dictatorship_def = new_definition (
  "q33481_is_dictatorship_def",
  ``q33481_is_dictatorship
      (f : ('i -> 'a -> 'a -> bool) -> 'a -> 'a -> bool)
      (V : 'i set) (X : 'a set) <=>
      ?i.
        i IN V /\
        !x y R.
          x IN X /\
          y IN X /\
          q33481_profile V R /\
          q33481_strict_preference (R i) x y
          ==>
          q33481_strict_preference (f R) x y``);

val arrow =
  ``!(V : 'i set) (X : 'a set)
      (f : ('i -> 'a -> 'a -> bool) -> 'a -> 'a -> bool).
      FINITE V /\
      FINITE X /\
      q33481_social_welfare f V /\
      q33481_weak_pareto f V X /\
      q33481_ind_of_irr_alts f V X /\
      3 <= CARD X
      ==>
      q33481_is_dictatorship f V X``;
