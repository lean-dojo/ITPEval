(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q5638886, "Hahn embedding theorem": every linearly ordered abelian group
  embeds additively and order-preservingly into the real Hahn series indexed
  by its nonzero Archimedean classes, with matching leading class. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory;

val q5638886_ordered_add_comm_group_def = new_definition (
  "q5638886_ordered_add_comm_group_def",
  ``q5638886_ordered_add_comm_group
      (zero : 'a) (neg : 'a -> 'a) (add : 'a -> 'a -> 'a)
      (leq : 'a -> 'a -> bool) <=>
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add zero x = x /\ add x zero = x) /\
      (!x. add (neg x) x = zero /\ add x (neg x) = zero) /\
      (!x y. add x y = add y x) /\
      (!x. leq x x) /\
      (!x y. leq x y /\ leq y x ==> x = y) /\
      (!x y z. leq x y /\ leq y z ==> leq x z) /\
      (!x y. leq x y \/ leq y x) /\
      (!x y z. leq x y ==> leq (add z x) (add z y))``);

val q5638886_abs_def = new_definition (
  "q5638886_abs_def",
  ``q5638886_abs zero neg leq (x : 'a) =
      if leq zero x then x else neg x``);

val q5638886_nsmul_def = new_definition (
  "q5638886_nsmul_def",
  ``q5638886_nsmul zero add (n : num) (x : 'a) =
      FUNPOW (add x) n zero``);

val q5638886_dominated_def = new_definition (
  "q5638886_dominated_def",
  ``q5638886_dominated zero neg add leq (x : 'a) (y : 'a) <=>
      ?n : num.
        leq (q5638886_abs zero neg leq x)
            (q5638886_nsmul zero add n
              (q5638886_abs zero neg leq y))``);

val q5638886_arch_equiv_def = new_definition (
  "q5638886_arch_equiv_def",
  ``q5638886_arch_equiv zero neg add leq (x : 'a) (y : 'a) <=>
      q5638886_dominated zero neg add leq x y /\
      q5638886_dominated zero neg add leq y x``);

val q5638886_arch_class_def = new_definition (
  "q5638886_arch_class_def",
  ``q5638886_arch_class zero neg add leq (x : 'a) =
      {y | q5638886_arch_equiv zero neg add leq x y}``);

val q5638886_finite_arch_class_def = new_definition (
  "q5638886_finite_arch_class_def",
  ``q5638886_finite_arch_class zero neg add leq (C : 'a set) <=>
      ?x : 'a.
        x <> zero /\
        C = q5638886_arch_class zero neg add leq x``);

val q5638886_arch_class_le_def = new_definition (
  "q5638886_arch_class_le_def",
  ``q5638886_arch_class_le zero neg add leq
      (C : 'a set) (D : 'a set) <=>
      ?x y : 'a.
        x IN C /\
        y IN D /\
        q5638886_dominated zero neg add leq y x``);

val q5638886_arch_class_lt_def = new_definition (
  "q5638886_arch_class_lt_def",
  ``q5638886_arch_class_lt zero neg add leq
      (C : 'a set) (D : 'a set) <=>
      q5638886_arch_class_le zero neg add leq C D /\
      C <> D``);

val q5638886_hahn_series_def = new_definition (
  "q5638886_hahn_series_def",
  ``q5638886_hahn_series zero neg add leq
      (s : 'a set -> real) <=>
      (!C : 'a set.
        ~q5638886_finite_arch_class zero neg add leq C
        ==>
        s C = 0) /\
      !u : ('a set) set.
        u SUBSET
          {C |
            q5638886_finite_arch_class zero neg add leq C /\
            s C <> 0} /\
        u <> {}
        ==>
        ?C : 'a set.
          C IN u /\
          !D : 'a set.
            D IN u
            ==>
            q5638886_arch_class_le zero neg add leq C D``);

val q5638886_lex_le_def = new_definition (
  "q5638886_lex_le_def",
  ``q5638886_lex_le zero neg add leq
      (s : 'a set -> real) (t : 'a set -> real) <=>
      s = t \/
      ?C : 'a set.
        q5638886_finite_arch_class zero neg add leq C /\
        s C < t C /\
        !D : 'a set.
          q5638886_finite_arch_class zero neg add leq D /\
          q5638886_arch_class_lt zero neg add leq D C
          ==>
          s D = t D``);

val q5638886_leading_class_matches_def = new_definition (
  "q5638886_leading_class_matches_def",
  ``q5638886_leading_class_matches zero neg add leq
      (a : 'a) (s : 'a set -> real) <=>
      if a = zero then
        !C : 'a set. s C = 0
      else
        s (q5638886_arch_class zero neg add leq a) <> 0 /\
        !D : 'a set.
          q5638886_finite_arch_class zero neg add leq D /\
          q5638886_arch_class_lt zero neg add leq D
            (q5638886_arch_class zero neg add leq a)
          ==>
          s D = 0``);

val hahnEmbedding_isOrderedAddMonoid =
  ``!(zero : 'a) (neg : 'a -> 'a) (add : 'a -> 'a -> 'a)
      (leq : 'a -> 'a -> bool).
      q5638886_ordered_add_comm_group zero neg add leq
      ==>
      ?f : 'a -> ('a set -> real).
        (!x : 'a. q5638886_hahn_series zero neg add leq (f x)) /\
        (!C : 'a set. f zero C = 0) /\
        (!x y : 'a. !C : 'a set.
          f (add x y) C = f x C + f y C) /\
        (!x y : 'a.
          leq x y
          ==>
          q5638886_lex_le zero neg add leq (f x) (f y)) /\
        (!x y : 'a. f x = f y ==> x = y) /\
        !a : 'a.
          q5638886_leading_class_matches zero neg add leq a (f a)``;
