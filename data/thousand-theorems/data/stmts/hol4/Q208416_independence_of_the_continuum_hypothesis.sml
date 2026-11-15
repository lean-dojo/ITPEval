(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q208416 (thousand-theorems__hol4__Q208416), "Independence of the continuum
  hypothesis": countable first-order models of ZFC witness both CH and its
  negation, equivalently neither CH nor its negation is derivable from ZFC.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinTheory pred_setTheory;

val q208416_pair_num_def = new_definition (
  "q208416_pair_num_def",
  ``q208416_pair_num i j =
      ((i + j) * (i + j + 1)) DIV 2 + j``);

val q208416_valuation_def = new_definition (
  "q208416_valuation_def",
  ``q208416_valuation (M : num set) (v : num -> num) <=>
      !i. v i IN M``);

val q208416_tarski_def = new_definition (
  "q208416_tarski_def",
  ``q208416_tarski
      (mem : num -> num -> bool)
      (M : num set)
      (sat : (num -> num) -> num -> bool) <=>
      (!v i j.
         q208416_valuation M v ==>
         (sat v (5 * q208416_pair_num i j) <=> v i = v j)) /\
      (!v i j.
         q208416_valuation M v ==>
         (sat v (5 * q208416_pair_num i j + 1) <=>
          mem (v i) (v j))) /\
      (!v p.
         q208416_valuation M v ==>
         (sat v (5 * p + 2) <=> ~sat v p)) /\
      (!v p q.
         q208416_valuation M v ==>
         (sat v (5 * q208416_pair_num p q + 3) <=>
          sat v p /\ sat v q)) /\
      (!v i p.
         q208416_valuation M v ==>
         (sat v (5 * q208416_pair_num i p + 4) <=>
          ?x. x IN M /\ sat ((i =+ x) v) p))``);

val q208416_internal_subset_def = new_definition (
  "q208416_internal_subset_def",
  ``q208416_internal_subset
      (mem : num -> num -> bool) (M : num set) a b <=>
      a IN M /\ b IN M /\
      !x. x IN M /\ mem x a ==> mem x b``);

val q208416_empty_object_def = new_definition (
  "q208416_empty_object_def",
  ``q208416_empty_object
      (mem : num -> num -> bool) (M : num set) e <=>
      e IN M /\ !x. x IN M ==> ~mem x e``);

val q208416_singleton_def = new_definition (
  "q208416_singleton_def",
  ``q208416_singleton
      (mem : num -> num -> bool) (M : num set) x s <=>
      x IN M /\ s IN M /\
      !z. z IN M ==> (mem z s <=> z = x)``);

val q208416_unordered_pair_def = new_definition (
  "q208416_unordered_pair_def",
  ``q208416_unordered_pair
      (mem : num -> num -> bool) (M : num set) x y p <=>
      x IN M /\ y IN M /\ p IN M /\
      !z. z IN M ==> (mem z p <=> z = x \/ z = y)``);

val q208416_ordered_pair_def = new_definition (
  "q208416_ordered_pair_def",
  ``q208416_ordered_pair
      (mem : num -> num -> bool) (M : num set) x y p <=>
      ?sx xy.
        q208416_singleton mem M x sx /\
        q208416_unordered_pair mem M x y xy /\
        q208416_unordered_pair mem M sx xy p``);

val q208416_relates_def = new_definition (
  "q208416_relates_def",
  ``q208416_relates
      (mem : num -> num -> bool) (M : num set) f x y <=>
      ?p.
        p IN M /\
        q208416_ordered_pair mem M x y p /\
        mem p f``);

val q208416_function_between_def = new_definition (
  "q208416_function_between_def",
  ``q208416_function_between
      (mem : num -> num -> bool) (M : num set) f a b <=>
      f IN M /\ a IN M /\ b IN M /\
      (!p.
         p IN M /\ mem p f ==>
         ?x y.
           x IN M /\ y IN M /\
           mem x a /\ mem y b /\
           q208416_ordered_pair mem M x y p) /\
      (!x.
         x IN M /\ mem x a ==>
         ?y.
           y IN M /\ mem y b /\
           q208416_relates mem M f x y) /\
      (!x y z.
         x IN M /\ y IN M /\ z IN M /\
         mem x a /\ mem y b /\ mem z b /\
         q208416_relates mem M f x y /\
         q208416_relates mem M f x z
         ==> y = z)``);

val q208416_injection_def = new_definition (
  "q208416_injection_def",
  ``q208416_injection
      (mem : num -> num -> bool) (M : num set) f a b <=>
      q208416_function_between mem M f a b /\
      !x x' y.
        x IN M /\ x' IN M /\ y IN M /\
        mem x a /\ mem x' a /\ mem y b /\
        q208416_relates mem M f x y /\
        q208416_relates mem M f x' y
        ==> x = x'``);

val q208416_successor_def = new_definition (
  "q208416_successor_def",
  ``q208416_successor
      (mem : num -> num -> bool) (M : num set) x s <=>
      x IN M /\ s IN M /\
      !z. z IN M ==> (mem z s <=> mem z x \/ z = x)``);

val q208416_inductive_object_def = new_definition (
  "q208416_inductive_object_def",
  ``q208416_inductive_object
      (mem : num -> num -> bool) (M : num set) i <=>
      i IN M /\
      (?e. q208416_empty_object mem M e /\ mem e i) /\
      !x.
        x IN M /\ mem x i ==>
        ?s. q208416_successor mem M x s /\ mem s i``);

val q208416_omega_object_def = new_definition (
  "q208416_omega_object_def",
  ``q208416_omega_object
      (mem : num -> num -> bool) (M : num set) omega <=>
      q208416_inductive_object mem M omega /\
      !i.
        q208416_inductive_object mem M i ==>
        q208416_internal_subset mem M omega i``);

val q208416_powerset_object_def = new_definition (
  "q208416_powerset_object_def",
  ``q208416_powerset_object
      (mem : num -> num -> bool) (M : num set) a p <=>
      a IN M /\ p IN M /\
      !x.
        x IN M ==>
        (mem x p <=> q208416_internal_subset mem M x a)``);

val q208416_choice_function_def = new_definition (
  "q208416_choice_function_def",
  ``q208416_choice_function
      (mem : num -> num -> bool) (M : num set) a f <=>
      a IN M /\ f IN M /\
      (!p.
         p IN M /\ mem p f ==>
         ?x y.
           x IN M /\ y IN M /\
           mem x a /\ mem y x /\
           q208416_ordered_pair mem M x y p) /\
      (!x.
         x IN M /\ mem x a ==>
         ?y.
           y IN M /\ mem y x /\
           q208416_relates mem M f x y) /\
      (!x y z.
         x IN M /\ y IN M /\ z IN M /\
         q208416_relates mem M f x y /\
         q208416_relates mem M f x z
         ==> y = z)``);

val q208416_zfc_model_def = new_definition (
  "q208416_zfc_model_def",
  ``q208416_zfc_model
      (mem : num -> num -> bool)
      (M : num set)
      (sat : (num -> num) -> num -> bool) <=>
      q208416_tarski mem M sat /\
      (!x y.
         x IN M /\ y IN M /\
         (!z. z IN M ==> (mem z x <=> mem z y))
         ==> x = y) /\
      (?e. q208416_empty_object mem M e) /\
      (!x y.
         x IN M /\ y IN M ==>
         ?p. q208416_unordered_pair mem M x y p) /\
      (!a.
         a IN M ==>
         ?u.
           u IN M /\
           !z.
             z IN M ==>
             (mem z u <=>
              ?y. y IN M /\ mem y a /\ mem z y)) /\
      (!a.
         a IN M ==>
         ?p. q208416_powerset_object mem M a p) /\
      (?i. q208416_inductive_object mem M i) /\
      (!a.
         a IN M /\ (?x. x IN M /\ mem x a) ==>
         ?x.
           x IN M /\ mem x a /\
           !y. y IN M /\ mem y a ==> ~mem y x) /\
      (!phi v a.
         q208416_valuation M v /\ a IN M ==>
         ?b.
           b IN M /\
           !x.
             x IN M ==>
             (mem x b <=>
              mem x a /\ sat ((0 =+ x) v) phi)) /\
      (!phi v a.
         q208416_valuation M v /\ a IN M /\
         (!x.
            x IN M /\ mem x a ==>
            ?y.
              y IN M /\
              sat ((1 =+ y) ((0 =+ x) v)) phi /\
              (!y'.
                 y' IN M /\
                 sat ((1 =+ y') ((0 =+ x) v)) phi
                 ==> y' = y))
         ==>
         ?b.
           b IN M /\
           !y.
             y IN M ==>
             (mem y b <=>
              ?x.
                x IN M /\ mem x a /\
                sat ((1 =+ y) ((0 =+ x) v)) phi)) /\
      (!a.
         a IN M /\
         (!x.
            x IN M /\ mem x a ==>
            ?y. y IN M /\ mem y x)
         ==>
         ?f. q208416_choice_function mem M a f)``);

val q208416_CH_def = new_definition (
  "q208416_CH_def",
  ``q208416_CH
      (mem : num -> num -> bool) (M : num set) <=>
      ?omega p.
        q208416_omega_object mem M omega /\
        q208416_powerset_object mem M omega p /\
        !x.
          x IN M /\ q208416_internal_subset mem M x p
          ==>
          (?f. q208416_injection mem M f x omega) \/
          (?f. q208416_injection mem M f p x)``);

val independence_of_CH =
  ``(?M : num set.
       ?mem : num -> num -> bool.
       ?sat : (num -> num) -> num -> bool.
         q208416_zfc_model mem M sat /\
         q208416_CH mem M) /\
    (?M : num set.
       ?mem : num -> num -> bool.
       ?sat : (num -> num) -> num -> bool.
         q208416_zfc_model mem M sat /\
         ~q208416_CH mem M)``;
