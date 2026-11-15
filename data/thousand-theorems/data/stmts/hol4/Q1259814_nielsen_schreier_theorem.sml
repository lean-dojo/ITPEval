(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1259814, "Nielsen–Schreier theorem": every subgroup of a free group is
  free. Freeness is expressed by unique reduced signed words over a basis.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory groupTheory listTheory pred_setTheory;

val ns_word_eval_def = new_definition (
  "ns_word_eval_def",
  ``ns_word_eval (g : 'a group) (w : ('a # bool) list) =
      FOLDL g.op g.id
        (MAP (\p. if SND p then FST p else g.inv (FST p)) w)``);

val ns_reduced_word_def = new_definition (
  "ns_reduced_word_def",
  ``ns_reduced_word (b : 'a set) (w : ('a # bool) list) <=>
      EVERY (\p. FST p IN b) w /\
      !n. SUC n < LENGTH w ==>
          (FST (EL n w) <> FST (EL (SUC n) w) \/
           SND (EL n w) = SND (EL (SUC n) w))``);

val ns_is_free_group_def = new_definition (
  "ns_is_free_group_def",
  ``ns_is_free_group (g : 'a group) <=>
      Group g /\
      ?b : 'a set.
        b SUBSET g.carrier /\
        (!x. x IN g.carrier ==>
             ?w. ns_reduced_word b w /\ ns_word_eval g w = x) /\
        (!u v.
           ns_reduced_word b u /\
           ns_reduced_word b v /\
           ns_word_eval g u = ns_word_eval g v
           ==>
           u = v)``);

val subgroupIsFreeOfIsFree =
  ``!(g : 'a group) (h : 'a group).
      ns_is_free_group g /\ Subgroup h g
      ==>
      ns_is_free_group h``;
