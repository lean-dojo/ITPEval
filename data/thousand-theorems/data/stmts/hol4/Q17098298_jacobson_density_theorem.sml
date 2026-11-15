(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q17098298, "Jacobson density theorem": on an arbitrary semisimple left
  module, every self-map linear over the ring of module endomorphisms agrees
  on each finite subset with multiplication by one scalar. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val q17098298_ring_def = new_definition (
  "q17098298_ring_def",
  ``q17098298_ring
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (negR : 'r -> 'r) <=>
      (!a b. addR a b = addR b a) /\
      (!a b c. addR (addR a b) c = addR a (addR b c)) /\
      (!a. addR zeroR a = a) /\
      (!a. addR (negR a) a = zeroR) /\
      (!a b c. mulR (mulR a b) c = mulR a (mulR b c)) /\
      (!a. mulR oneR a = a) /\
      (!a. mulR a oneR = a) /\
      (!a b c. mulR a (addR b c) =
                 addR (mulR a b) (mulR a c)) /\
      (!a b c. mulR (addR a b) c =
                 addR (mulR a c) (mulR b c))``);

val q17098298_add_comm_group_def = new_definition (
  "q17098298_add_comm_group_def",
  ``q17098298_add_comm_group
      (zeroM : 'm) (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm) <=>
      (!x y. addM x y = addM y x) /\
      (!x y z. addM (addM x y) z = addM x (addM y z)) /\
      (!x. addM zeroM x = x) /\
      (!x. addM (negM x) x = zeroM)``);

val q17098298_module_def = new_definition (
  "q17098298_module_def",
  ``q17098298_module
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (smul : 'r -> 'm -> 'm) <=>
      (!x. smul oneR x = x) /\
      (!a b x. smul (mulR a b) x = smul a (smul b x)) /\
      (!a b x. smul (addR a b) x =
                 addM (smul a x) (smul b x)) /\
      (!a x y. smul a (addM x y) =
                 addM (smul a x) (smul a y)) /\
      (!x. smul zeroR x = zeroM) /\
      (!a. smul a zeroM = zeroM)``);

val q17098298_submodule_def = new_definition (
  "q17098298_submodule_def",
  ``q17098298_submodule
      (zeroM : 'm) (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm)
      (smul : 'r -> 'm -> 'm) (p : 'm -> bool) <=>
      p zeroM /\
      (!x y. p x /\ p y ==> p (addM x y)) /\
      (!x. p x ==> p (negM x)) /\
      (!a x. p x ==> p (smul a x))``);

val q17098298_complement_def = new_definition (
  "q17098298_complement_def",
  ``q17098298_complement
      (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (p : 'm -> bool) (q : 'm -> bool) <=>
      (!x. p x /\ q x ==> x = zeroM) /\
      (!x. ?y z. p y /\ q z /\ x = addM y z)``);

val q17098298_semisimple_module_def = new_definition (
  "q17098298_semisimple_module_def",
  ``q17098298_semisimple_module
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (negR : 'r -> 'r)
      (zeroM : 'm) (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm)
      (smul : 'r -> 'm -> 'm) <=>
      q17098298_ring zeroR oneR addR mulR negR /\
      q17098298_add_comm_group zeroM addM negM /\
      q17098298_module zeroR oneR addR mulR zeroM addM smul /\
      !p : 'm -> bool.
        q17098298_submodule zeroM addM negM smul p
        ==>
        ?q : 'm -> bool.
          q17098298_submodule zeroM addM negM smul q /\
          q17098298_complement zeroM addM p q``);

val q17098298_linear_endomorphism_def = new_definition (
  "q17098298_linear_endomorphism_def",
  ``q17098298_linear_endomorphism
      (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (smul : 'r -> 'm -> 'm) (g : 'm -> 'm) <=>
      g zeroM = zeroM /\
      (!x y. g (addM x y) = addM (g x) (g y)) /\
      (!a x. g (smul a x) = smul a (g x))``);

val q17098298_endomorphism_linear_def = new_definition (
  "q17098298_endomorphism_linear_def",
  ``q17098298_endomorphism_linear
      (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (smul : 'r -> 'm -> 'm) (f : 'm -> 'm) <=>
      f zeroM = zeroM /\
      (!x y. f (addM x y) = addM (f x) (f y)) /\
      (!g : 'm -> 'm.
        q17098298_linear_endomorphism zeroM addM smul g
        ==>
        !x. f (g x) = g (f x))``);

val jacobson_density_statement =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (negR : 'r -> 'r)
      (zeroM : 'm) (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm)
      (smul : 'r -> 'm -> 'm)
      (f : 'm -> 'm) (s : 'm set).
      q17098298_semisimple_module
        zeroR oneR addR mulR negR zeroM addM negM smul /\
      q17098298_endomorphism_linear zeroM addM smul f /\
      FINITE s
      ==>
      ?r : 'r. !m. m IN s ==> f m = smul r m``;
