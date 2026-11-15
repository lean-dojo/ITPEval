(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q7888360, "Structure theorem for finitely generated modules over a
  principal ideal domain": every finitely generated module over a
  commutative principal ideal domain is linearly equivalent to a finite-rank
  free module times a finite direct sum of cyclic prime-power quotients.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinTheory pairTheory pred_setTheory;

val q7888360_comm_ring_def = new_definition (
  "q7888360_comm_ring_def",
  ``q7888360_comm_ring (zeroR : 'r) (oneR : 'r) (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r) (negR : 'r -> 'r) <=> (!a b c. addR (addR a b) c = addR a (addR b c)) /\ (!a b. addR a b = addR b a) /\ (!a. addR zeroR a = a) /\ (!a. addR (negR a) a = zeroR) /\ (!a b c. mulR (mulR a b) c = mulR a (mulR b c)) /\ (!a b. mulR a b = mulR b a) /\ (!a. mulR oneR a = a) /\ (!a b c. mulR a (addR b c) = addR (mulR a b) (mulR a c))``);

val q7888360_domain_def = new_definition (
  "q7888360_domain_def",
  ``q7888360_domain (zeroR : 'r) (oneR : 'r) (mulR : 'r -> 'r -> 'r) <=> zeroR <> oneR /\ (!a b. mulR a b = zeroR ==> a = zeroR \/ b = zeroR)``);

val q7888360_ideal_def = new_definition (
  "q7888360_ideal_def",
  ``q7888360_ideal (zeroR : 'r) (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r) (negR : 'r -> 'r) (ideal : 'r set) <=> zeroR IN ideal /\ (!a b. a IN ideal /\ b IN ideal ==> addR a b IN ideal) /\ (!a. a IN ideal ==> negR a IN ideal) /\ (!r a. a IN ideal ==> mulR r a IN ideal)``);

val q7888360_principal_ideal_def = new_definition (
  "q7888360_principal_ideal_def",
  ``q7888360_principal_ideal (mulR : 'r -> 'r -> 'r) (a : 'r) = {x | ?r. x = mulR r a}``);

val q7888360_principal_ideal_ring_def = new_definition (
  "q7888360_principal_ideal_ring_def",
  ``q7888360_principal_ideal_ring (zeroR : 'r) (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r) (negR : 'r -> 'r) <=> !ideal : 'r set. q7888360_ideal zeroR addR mulR negR ideal ==> ?a. ideal = q7888360_principal_ideal mulR a``);

val q7888360_module_def = new_definition (
  "q7888360_module_def",
  ``q7888360_module (zeroR : 'r) (oneR : 'r) (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r) (zeroM : 'm) (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm) (smul : 'r -> 'm -> 'm) <=> (!x y z. addM (addM x y) z = addM x (addM y z)) /\ (!x y. addM x y = addM y x) /\ (!x. addM zeroM x = x) /\ (!x. addM (negM x) x = zeroM) /\ (!a x y. smul a (addM x y) = addM (smul a x) (smul a y)) /\ (!a b x. smul (addR a b) x = addM (smul a x) (smul b x)) /\ (!a b x. smul (mulR a b) x = smul a (smul b x)) /\ (!x. smul oneR x = x) /\ (!x. smul zeroR x = zeroM) /\ (!a. smul a zeroM = zeroM)``);

val q7888360_submodule_def = new_definition (
  "q7888360_submodule_def",
  ``q7888360_submodule (zeroM : 'm) (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm) (smul : 'r -> 'm -> 'm) (submodule : 'm set) <=> zeroM IN submodule /\ (!x y. x IN submodule /\ y IN submodule ==> addM x y IN submodule) /\ (!x. x IN submodule ==> negM x IN submodule) /\ (!a x. x IN submodule ==> smul a x IN submodule)``);

val q7888360_span_def = new_definition (
  "q7888360_span_def",
  ``q7888360_span (zeroM : 'm) (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm) (smul : 'r -> 'm -> 'm) (s : 'm set) = {x | !submodule : 'm set. q7888360_submodule zeroM addM negM smul submodule /\ s SUBSET submodule ==> x IN submodule}``);

val q7888360_finitely_generated_def = new_definition (
  "q7888360_finitely_generated_def",
  ``q7888360_finitely_generated (zeroM : 'm) (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm) (smul : 'r -> 'm -> 'm) <=> ?s : 'm set. FINITE s /\ q7888360_span zeroM addM negM smul s = UNIV``);

val q7888360_unit_def = new_definition (
  "q7888360_unit_def",
  ``q7888360_unit (oneR : 'r) (mulR : 'r -> 'r -> 'r) (a : 'r) <=> ?b. mulR a b = oneR``);

val q7888360_irreducible_def = new_definition (
  "q7888360_irreducible_def",
  ``q7888360_irreducible (oneR : 'r) (mulR : 'r -> 'r -> 'r) (p : 'r) <=> ~q7888360_unit oneR mulR p /\ (!a b. p = mulR a b ==> q7888360_unit oneR mulR a \/ q7888360_unit oneR mulR b)``);

val q7888360_pow_def = new_definition (
  "q7888360_pow_def",
  ``q7888360_pow (oneR : 'r) (mulR : 'r -> 'r -> 'r) (a : 'r) (n : num) = FUNPOW (mulR a) n oneR``);

val q7888360_class_def = new_definition (
  "q7888360_class_def",
  ``q7888360_class (addR : 'r -> 'r -> 'r) (negR : 'r -> 'r) (ideal : 'r set) (r : 'r) = {x | addR x (negR r) IN ideal}``);

val q7888360_quotient_carrier_def = new_definition (
  "q7888360_quotient_carrier_def",
  ``q7888360_quotient_carrier (addR : 'r -> 'r -> 'r) (negR : 'r -> 'r) (ideal : 'r set) = {cls | ?r. cls = q7888360_class addR negR ideal r}``);

val q7888360_quotient_add_def = new_definition (
  "q7888360_quotient_add_def",
  ``q7888360_quotient_add (addR : 'r -> 'r -> 'r) (negR : 'r -> 'r) (ideal : 'r set) (cls1 : 'r set) (cls2 : 'r set) = {z | ?x y. x IN cls1 /\ y IN cls2 /\ addR z (negR (addR x y)) IN ideal}``);

val q7888360_quotient_smul_def = new_definition (
  "q7888360_quotient_smul_def",
  ``q7888360_quotient_smul (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r) (negR : 'r -> 'r) (ideal : 'r set) (a : 'r) (cls : 'r set) = {z | ?x. x IN cls /\ addR z (negR (mulR a x)) IN ideal}``);

val q7888360_target_carrier_def = new_definition (
  "q7888360_target_carrier_def",
  ``q7888360_target_carrier (zeroR : 'r) (oneR : 'r) (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r) (negR : 'r -> 'r) (n : num) (indices : num set) (p : num -> 'r) (e : num -> num) = {q : (num -> 'r) # (num -> 'r set) | (!j. n <= j ==> FST q j = zeroR) /\ (!i. i IN indices ==> SND q i IN q7888360_quotient_carrier addR negR (q7888360_principal_ideal mulR (q7888360_pow oneR mulR (p i) (e i)))) /\ (!i. ~(i IN indices) ==> SND q i = {})}``);

val q7888360_target_add_def = new_definition (
  "q7888360_target_add_def",
  ``q7888360_target_add (oneR : 'r) (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r) (negR : 'r -> 'r) (indices : num set) (p : num -> 'r) (e : num -> num) (q : (num -> 'r) # (num -> 'r set)) (r : (num -> 'r) # (num -> 'r set)) = ((\j. addR (FST q j) (FST r j)), (\i. if i IN indices then q7888360_quotient_add addR negR (q7888360_principal_ideal mulR (q7888360_pow oneR mulR (p i) (e i))) (SND q i) (SND r i) else {}))``);

val q7888360_target_smul_def = new_definition (
  "q7888360_target_smul_def",
  ``q7888360_target_smul (oneR : 'r) (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r) (negR : 'r -> 'r) (indices : num set) (p : num -> 'r) (e : num -> num) (a : 'r) (q : (num -> 'r) # (num -> 'r set)) = ((\j. mulR a (FST q j)), (\i. if i IN indices then q7888360_quotient_smul addR mulR negR (q7888360_principal_ideal mulR (q7888360_pow oneR mulR (p i) (e i))) a (SND q i) else {}))``);

val Module_equiv_free_prod_directSum =
  ``!(zeroR : 'r) (oneR : 'r) (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r) (negR : 'r -> 'r) (zeroM : 'm) (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm) (smul : 'r -> 'm -> 'm). q7888360_comm_ring zeroR oneR addR mulR negR /\ q7888360_domain zeroR oneR mulR /\ q7888360_principal_ideal_ring zeroR addR mulR negR /\ q7888360_module zeroR oneR addR mulR zeroM addM negM smul /\ q7888360_finitely_generated zeroM addM negM smul ==> ?n : num. ?indices : num set. ?p : num -> 'r. ?e : num -> num. FINITE indices /\ (!i. i IN indices ==> q7888360_irreducible oneR mulR (p i)) /\ ?f : 'm -> (num -> 'r) # (num -> 'r set). BIJ f UNIV (q7888360_target_carrier zeroR oneR addR mulR negR n indices p e) /\ (!x y. f (addM x y) = q7888360_target_add oneR addR mulR negR indices p e (f x) (f y)) /\ (!a x. f (smul a x) = q7888360_target_smul oneR addR mulR negR indices p e a (f x))``;
