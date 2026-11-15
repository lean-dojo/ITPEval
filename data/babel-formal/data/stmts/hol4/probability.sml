(*
  Statement-only formalization of the Babel-formal artifact probability: abstract event
  algebra and finite probability identities over a commutative integral-domain-like carrier.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib arithmeticTheory listTheory;

val _ = new_theory "hello";

val babel_mynat_add_def = new_definition (
  "babel_mynat_add_def",
  ``babel_mynat_add (n : num) m = n + m``);

val babel_InL_def = new_definition (
  "babel_InL_def",
  ``babel_InL (x : 'a) (xs : 'a list) <=> MEM x xs``);

val babel_NoDupL_def = new_definition (
  "babel_NoDupL_def",
  ``babel_NoDupL (xs : 'a list) <=> ALL_DISTINCT xs``);

val babel_mapL_def = new_definition (
  "babel_mapL_def",
  ``babel_mapL (f : 'a -> 'b) (xs : 'a list) = MAP f xs``);

val babel_fold_add_def = new_definition (
  "babel_fold_add_def",
  ``babel_fold_add (add : 'a -> 'a -> 'a) (zero : 'a)
      (xs : 'a list) =
      FOLDR add zero xs``);

val mynat_add_O_left =
  ``!(m : num). babel_mynat_add 0 m = m``;

val mynat_add_S_left =
  ``!(n : num) m.
      babel_mynat_add (SUC n) m = SUC (babel_mynat_add n m)``;

val babel_integral_domain_def = new_definition (
  "babel_integral_domain_def",
  ``babel_integral_domain
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) <=>
      ~(oneR = zeroR) /\
      (!x y. addR x y = addR y x) /\
      (!x y z. addR (addR x y) z = addR x (addR y z)) /\
      (!x. addR x zeroR = x) /\
      (!x. addR x (oppR x) = zeroR) /\
      (!x y. mulR x y = mulR y x) /\
      (!x y z. mulR (mulR x y) z = mulR x (mulR y z)) /\
      (!x. mulR x oneR = x) /\
      (!x y z. mulR x (addR y z) = addR (mulR x y) (mulR x z)) /\
      (!x. mulR x zeroR = zeroR) /\
      (!x y. mulR x y = zeroR ==> x = zeroR \/ y = zeroR)``);

val babel_subR_def = new_definition (
  "babel_subR_def",
  ``babel_subR (addR : 'r -> 'r -> 'r) (oppR : 'r -> 'r)
      (x : 'r) y =
      addR x (oppR y)``);

val babel_ev_false_def = new_definition (
  "babel_ev_false_def",
  ``babel_ev_false : 'w -> bool = (\w. F)``);

val babel_ev_true_def = new_definition (
  "babel_ev_true_def",
  ``babel_ev_true : 'w -> bool = (\w. T)``);

val babel_ev_inter_def = new_definition (
  "babel_ev_inter_def",
  ``babel_ev_inter (A : 'w -> bool) (B : 'w -> bool) =
      (\w. A w /\ B w)``);

val babel_ev_union_def = new_definition (
  "babel_ev_union_def",
  ``babel_ev_union (A : 'w -> bool) (B : 'w -> bool) =
      (\w. A w \/ B w)``);

val babel_ev_compl_def = new_definition (
  "babel_ev_compl_def",
  ``babel_ev_compl (A : 'w -> bool) = (\w. ~(A w))``);

val babel_ev_diff_def = new_definition (
  "babel_ev_diff_def",
  ``babel_ev_diff (A : 'w -> bool) (B : 'w -> bool) =
      (\w. A w /\ ~(B w))``);

val babel_disjoint_def = new_definition (
  "babel_disjoint_def",
  ``babel_disjoint (A : 'w -> bool) (B : 'w -> bool) <=>
      !w. ~(A w /\ B w)``);

val babel_pairwise_disjoint_def = new_definition (
  "babel_pairwise_disjoint_def",
  ``babel_pairwise_disjoint (xs : ('w -> bool) list) <=>
      !i j.
        i < j /\ j < LENGTH xs ==>
        babel_disjoint (EL i xs) (EL j xs)``);

val babel_bigUnion_def = new_definition (
  "babel_bigUnion_def",
  ``babel_bigUnion (xs : ('w -> bool) list) =
      (\w. ?A. MEM A xs /\ A w)``);

val babel_indep_def = new_definition (
  "babel_indep_def",
  ``babel_indep
      (prob : ('w -> bool) -> 'r) (mulR : 'r -> 'r -> 'r)
      (A : 'w -> bool) B <=>
      prob (babel_ev_inter A B) = mulR (prob A) (prob B)``);

val babel_inclusion_exclusion_three_def = new_definition (
  "babel_inclusion_exclusion_three_def",
  ``babel_inclusion_exclusion_three
      (addR : 'r -> 'r -> 'r) (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (A : 'w -> bool) (B : 'w -> bool) (C : 'w -> bool) <=>
      prob (babel_ev_union (babel_ev_union A B) C) =
      addR (prob A)
        (addR (prob B)
          (addR (prob C)
            (oppR
              (addR (prob (babel_ev_inter A B))
                (addR (prob (babel_ev_inter A C))
                  (addR (prob (babel_ev_inter B C))
                    (oppR
                      (prob
                        (babel_ev_inter (babel_ev_inter A B) C)))))))))``);

val ev_inter_comm =
  ``!(A : 'w -> bool) B w.
      (babel_ev_inter A B w <=> babel_ev_inter B A w)``;

val ev_union_comm =
  ``!(A : 'w -> bool) B w.
      (babel_ev_union A B w <=> babel_ev_union B A w)``;

val ev_inter_assoc =
  ``!(A : 'w -> bool) B C w.
      (babel_ev_inter (babel_ev_inter A B) C w <=>
       babel_ev_inter A (babel_ev_inter B C) w)``;

val ev_union_assoc =
  ``!(A : 'w -> bool) B C w.
      (babel_ev_union (babel_ev_union A B) C w <=>
       babel_ev_union A (babel_ev_union B C) w)``;

val ev_inter_distrib_left =
  ``!(A : 'w -> bool) B C w.
      (babel_ev_inter A (babel_ev_union B C) w <=>
       babel_ev_union
         (babel_ev_inter A B) (babel_ev_inter A C) w)``;

val babel_probability_context_def = new_definition (
  "babel_probability_context_def",
  ``babel_probability_context
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (cprob : ('w -> bool) -> ('w -> bool) -> 'r) <=>
      babel_integral_domain zeroR oneR addR mulR oppR /\
      (!(A : 'w -> bool) (B : 'w -> bool).
         (!(w : 'w). A w <=> B w) ==>
         prob A = prob B) /\
      prob (babel_ev_false : 'w -> bool) = zeroR /\
      prob (babel_ev_true : 'w -> bool) = oneR /\
      (!(A : 'w -> bool) (B : 'w -> bool).
         prob (babel_ev_union A B) =
         addR (prob A)
           (addR (prob B) (oppR (prob (babel_ev_inter A B))))) /\
      (!(A : 'w -> bool).
         prob (babel_ev_compl A) =
         addR oneR (oppR (prob A))) /\
      (!(A : 'w -> bool) (B : 'w -> bool).
         prob (babel_ev_inter A B) =
         mulR (cprob A B) (prob B)) /\
      oppR zeroR = zeroR /\
      (!(x : 'r). oppR (oppR x) = x) /\
      (!(x : 'r) (y : 'r).
         mulR x (oppR y) = oppR (mulR x y)) /\
      (!(x : 'r) (y : 'r).
         mulR (oppR x) y = oppR (mulR x y)) /\
      (!(A : 'w -> bool) (B : 'w -> bool).
         babel_disjoint A B ==>
         prob (babel_ev_union A B) = addR (prob A) (prob B)) /\
      (!(A : 'w -> bool) (xs : ('w -> bool) list).
         babel_pairwise_disjoint (A::xs) ==>
         babel_disjoint A (babel_bigUnion xs))``);

val prob_union_comm =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (cprob : ('w -> bool) -> ('w -> bool) -> 'r)
      (A : 'w -> bool) B.
      babel_probability_context
        zeroR oneR addR mulR oppR prob cprob ==>
      prob (babel_ev_union A B) = prob (babel_ev_union B A)``;

val prob_union_idem =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (cprob : ('w -> bool) -> ('w -> bool) -> 'r)
      (A : 'w -> bool).
      babel_probability_context
        zeroR oneR addR mulR oppR prob cprob ==>
      prob (babel_ev_union A A) = prob A``;

val prob_diff =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (cprob : ('w -> bool) -> ('w -> bool) -> 'r)
      (A : 'w -> bool) B.
      babel_probability_context
        zeroR oneR addR mulR oppR prob cprob ==>
      prob (babel_ev_diff A B) =
      babel_subR addR oppR (prob A) (prob (babel_ev_inter A B))``;

val bayes_symm =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (cprob : ('w -> bool) -> ('w -> bool) -> 'r)
      (A : 'w -> bool) B.
      babel_probability_context
        zeroR oneR addR mulR oppR prob cprob ==>
      mulR (cprob A B) (prob B) =
      mulR (cprob B A) (prob A)``;

val law_total_prob =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (cprob : ('w -> bool) -> ('w -> bool) -> 'r)
      (A : 'w -> bool) B.
      babel_probability_context
        zeroR oneR addR mulR oppR prob cprob ==>
      prob A =
      addR
        (mulR (cprob A B) (prob B))
        (mulR (cprob A (babel_ev_compl B))
          (prob (babel_ev_compl B)))``;

val prob_union_indep =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (cprob : ('w -> bool) -> ('w -> bool) -> 'r)
      (A : 'w -> bool) B.
      babel_probability_context
        zeroR oneR addR mulR oppR prob cprob ==>
      babel_indep prob mulR A B ==>
      prob (babel_ev_union A B) =
      addR (prob A)
        (addR (prob B) (oppR (mulR (prob A) (prob B))))``;

val indep_compl_right =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (cprob : ('w -> bool) -> ('w -> bool) -> 'r)
      (A : 'w -> bool) B.
      babel_probability_context
        zeroR oneR addR mulR oppR prob cprob ==>
      babel_indep prob mulR A B ==>
      babel_indep prob mulR A (babel_ev_compl B)``;

val indep_symm =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (cprob : ('w -> bool) -> ('w -> bool) -> 'r)
      (A : 'w -> bool) B.
      babel_probability_context
        zeroR oneR addR mulR oppR prob cprob ==>
      babel_indep prob mulR A B ==>
      babel_indep prob mulR B A``;

val indep_compl_left =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (cprob : ('w -> bool) -> ('w -> bool) -> 'r)
      (A : 'w -> bool) B.
      babel_probability_context
        zeroR oneR addR mulR oppR prob cprob ==>
      babel_indep prob mulR A B ==>
      babel_indep prob mulR (babel_ev_compl A) B``;

val indep_compl_both =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (cprob : ('w -> bool) -> ('w -> bool) -> 'r)
      (A : 'w -> bool) B.
      babel_probability_context
        zeroR oneR addR mulR oppR prob cprob ==>
      babel_indep prob mulR A B ==>
      babel_indep prob mulR
        (babel_ev_compl A) (babel_ev_compl B)``;

val prob_bigUnion_disjoint =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (cprob : ('w -> bool) -> ('w -> bool) -> 'r)
      (xs : ('w -> bool) list).
      babel_probability_context
        zeroR oneR addR mulR oppR prob cprob ==>
      babel_pairwise_disjoint xs ==>
      prob (babel_bigUnion xs) =
      babel_fold_add addR zeroR (babel_mapL prob xs)``;

val prob_bigUnion_disjoint_zero =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (cprob : ('w -> bool) -> ('w -> bool) -> 'r)
      (xs : ('w -> bool) list).
      babel_probability_context
        zeroR oneR addR mulR oppR prob cprob ==>
      babel_pairwise_disjoint xs ==>
      (!A. babel_InL A xs ==> prob A = zeroR) ==>
      prob (babel_bigUnion xs) = zeroR``;

val inclusion_exclusion_three =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (prob : ('w -> bool) -> 'r)
      (cprob : ('w -> bool) -> ('w -> bool) -> 'r)
      (A : 'w -> bool) B C.
      babel_probability_context
        zeroR oneR addR mulR oppR prob cprob ==>
      babel_inclusion_exclusion_three addR oppR prob A B C``;

val _ = export_theory();
