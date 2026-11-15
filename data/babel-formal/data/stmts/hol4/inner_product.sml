(*
  Statement-only formalization of the Babel-formal artifact inner_product:
  abstract vector spaces with a symmetric bilinear form and its sum,
  difference, Pythagoras, and parallelogram identities. This file contains no
  proof.
*)

open HolKernel Parse boolLib;

val _ = new_theory "hello";

val inner_product_context_def = new_definition (
  "inner_product_context_def",
  ``inner_product_context
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (oppV : 'v -> 'v)
      (smul : 'r -> 'v -> 'v) (ip : 'v -> 'v -> 'r) <=>
      (!x y. addR x y = addR y x) /\
      (!x y z. addR (addR x y) z = addR x (addR y z)) /\
      (!x. addR x zeroR = x) /\
      (!x. addR zeroR x = x) /\
      (!x. addR x (oppR x) = zeroR) /\
      (!x y. mulR x y = mulR y x) /\
      (!x y z. mulR (mulR x y) z = mulR x (mulR y z)) /\
      (!x. mulR x oneR = x) /\
      (!x y z.
         mulR x (addR y z) = addR (mulR x y) (mulR x z)) /\
      (!x y. oppR (addR x y) = addR (oppR x) (oppR y)) /\
      (!x. mulR (oppR oneR) x = oppR x) /\
      (!x. oppR (oppR x) = x) /\
      (!u v. addV u v = addV v u) /\
      (!u v w. addV (addV u v) w = addV u (addV v w)) /\
      (!u. addV u zeroV = u) /\
      (!u. addV u (oppV u) = zeroV) /\
      (!a u v. smul a (addV u v) = addV (smul a u) (smul a v)) /\
      (!a b u. smul (addR a b) u = addV (smul a u) (smul b u)) /\
      (!a b u. smul (mulR a b) u = smul a (smul b u)) /\
      (!u. smul oneR u = u) /\
      (!a. smul a zeroV = zeroV) /\
      (!u. oppV u = smul (oppR oneR) u) /\
      (!u v w. ip (addV u v) w = addR (ip u w) (ip v w)) /\
      (!a u v. ip (smul a u) v = mulR a (ip u v)) /\
      (!u v w. ip u (addV v w) = addR (ip u v) (ip u w)) /\
      (!a u v. ip u (smul a v) = mulR a (ip u v)) /\
      (!u v. ip u v = ip v u)``);

val inner_subV_def = new_definition (
  "inner_subV_def",
  ``inner_subV (addV : 'v -> 'v -> 'v) (oppV : 'v -> 'v) u v =
      addV u (oppV v)``);

val ip_neg_left =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (oppV : 'v -> 'v)
      (smul : 'r -> 'v -> 'v) (ip : 'v -> 'v -> 'r).
      inner_product_context zeroR oneR addR mulR oppR
        zeroV addV oppV smul ip ==>
      !u v. ip (oppV u) v = oppR (ip u v)``;

val ip_neg_right =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (oppV : 'v -> 'v)
      (smul : 'r -> 'v -> 'v) (ip : 'v -> 'v -> 'r).
      inner_product_context zeroR oneR addR mulR oppR
        zeroV addV oppV smul ip ==>
      !u v. ip u (oppV v) = oppR (ip u v)``;

val ip_add_add =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (oppV : 'v -> 'v)
      (smul : 'r -> 'v -> 'v) (ip : 'v -> 'v -> 'r).
      inner_product_context zeroR oneR addR mulR oppR
        zeroV addV oppV smul ip ==>
      !u v.
        ip (addV u v) (addV u v) =
          addR (addR (ip u u) (ip v u))
               (addR (ip u v) (ip v v))``;

val ip_sub_sub =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (oppV : 'v -> 'v)
      (smul : 'r -> 'v -> 'v) (ip : 'v -> 'v -> 'r).
      inner_product_context zeroR oneR addR mulR oppR
        zeroV addV oppV smul ip ==>
      !u v.
        ip (inner_subV addV oppV u v) (inner_subV addV oppV u v) =
          addR (addR (ip u u) (oppR (ip v u)))
               (addR (oppR (ip u v)) (ip v v))``;

val pythagoras =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (oppV : 'v -> 'v)
      (smul : 'r -> 'v -> 'v) (ip : 'v -> 'v -> 'r).
      inner_product_context zeroR oneR addR mulR oppR
        zeroV addV oppV smul ip ==>
      !u v.
        ip u v = zeroR ==>
        ip (addV u v) (addV u v) = addR (ip u u) (ip v v)``;

val parallelogram =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (oppV : 'v -> 'v)
      (smul : 'r -> 'v -> 'v) (ip : 'v -> 'v -> 'r).
      inner_product_context zeroR oneR addR mulR oppR
        zeroV addV oppV smul ip ==>
      !u v.
        addR (ip (addV u v) (addV u v))
             (ip (inner_subV addV oppV u v)
                 (inner_subV addV oppV u v)) =
          addR
            (addR (addR (ip u u) (ip v u))
                  (addR (ip u v) (ip v v)))
            (addR (addR (ip u u) (oppR (ip v u)))
                  (addR (oppR (ip u v)) (ip v v)))``;

val _ = export_theory();
