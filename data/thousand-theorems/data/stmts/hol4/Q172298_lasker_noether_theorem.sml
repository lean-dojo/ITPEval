(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q172298, "Lasker–Noether theorem": a finite primary decomposition of a
  submodule can be replaced by one whose colon-ideal radicals are pairwise
  distinct. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinTheory pred_setTheory;

val q172298_comm_semiring_def = new_definition (
  "q172298_comm_semiring_def",
  ``q172298_comm_semiring
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r) <=>
      (!a b. addR a b = addR b a) /\
      (!a b c. addR (addR a b) c = addR a (addR b c)) /\
      (!a. addR zeroR a = a) /\
      (!a b. mulR a b = mulR b a) /\
      (!a b c. mulR (mulR a b) c = mulR a (mulR b c)) /\
      (!a. mulR oneR a = a) /\
      (!a b c. mulR a (addR b c) = addR (mulR a b) (mulR a c)) /\
      (!a. mulR zeroR a = zeroR)``);

val q172298_module_def = new_definition (
  "q172298_module_def",
  ``q172298_module
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (smul : 'r -> 'm -> 'm) <=>
      (!x y. addM x y = addM y x) /\
      (!x y z. addM (addM x y) z = addM x (addM y z)) /\
      (!x. addM zeroM x = x) /\
      (!a x y. smul a (addM x y) = addM (smul a x) (smul a y)) /\
      (!a. smul a zeroM = zeroM) /\
      (!a b x. smul (addR a b) x = addM (smul a x) (smul b x)) /\
      (!a b x. smul (mulR a b) x = smul a (smul b x)) /\
      (!x. smul oneR x = x) /\
      (!x. smul zeroR x = zeroM)``);

val q172298_submodule_def = new_definition (
  "q172298_submodule_def",
  ``q172298_submodule
      (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (smul : 'r -> 'm -> 'm) (N : 'm set) <=>
      zeroM IN N /\
      (!x y. x IN N /\ y IN N ==> addM x y IN N) /\
      (!a x. x IN N ==> smul a x IN N)``);

val q172298_pow_def = new_definition (
  "q172298_pow_def",
  ``q172298_pow (oneR : 'r) (mulR : 'r -> 'r -> 'r)
      (a : 'r) (n : num) =
      FUNPOW (mulR a) n oneR``);

val q172298_radical_colon_def = new_definition (
  "q172298_radical_colon_def",
  ``q172298_radical_colon
      (oneR : 'r) (mulR : 'r -> 'r -> 'r)
      (smul : 'r -> 'm -> 'm) (N : 'm set) (a : 'r) <=>
      ?n : num.
        !x : 'm. smul (q172298_pow oneR mulR a n) x IN N``);

val q172298_primary_def = new_definition (
  "q172298_primary_def",
  ``q172298_primary
      (oneR : 'r) (mulR : 'r -> 'r -> 'r)
      (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (smul : 'r -> 'm -> 'm) (N : 'm set) <=>
      q172298_submodule zeroM addM smul N /\
      ~(!x : 'm. x IN N) /\
      (!a : 'r. !x : 'm.
        smul a x IN N
        ==>
        x IN N \/ q172298_radical_colon oneR mulR smul N a)``);

val isPrimary_decomposition_pairwise_ne_radical =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (smul : 'r -> 'm -> 'm)
      (N : 'm set) (s : ('m set) set).
      q172298_comm_semiring zeroR oneR addR mulR /\
      q172298_module zeroR oneR addR mulR zeroM addM smul /\
      q172298_submodule zeroM addM smul N /\
      FINITE s /\
      (!J. J IN s ==>
        q172298_primary oneR mulR zeroM addM smul J) /\
      (!x. x IN N <=> !J. J IN s ==> x IN J)
      ==>
      ?t : ('m set) set.
        FINITE t /\
        (!x. x IN N <=> !J. J IN t ==> x IN J) /\
        (!J. J IN t ==>
          q172298_primary oneR mulR zeroM addM smul J) /\
        (!I J.
          I IN t /\ J IN t /\ I <> J
          ==>
          ?a : 'r.
            q172298_radical_colon oneR mulR smul I a <>
            q172298_radical_colon oneR mulR smul J a)``;
