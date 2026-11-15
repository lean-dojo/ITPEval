(*
  Statement-only formalization of the Babel-formal artifact linear_map: kernels
  and images of linear maps are closed under vector addition and scalar
  multiplication. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_theory "hello";

val babel_field_def = new_definition (
  "babel_field_def",
  ``babel_field (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) <=>
      (!x y. addR x y = addR y x) /\
      (!x y z. addR (addR x y) z = addR x (addR y z)) /\
      (!x. addR x zeroR = x) /\
      (!x. addR x (oppR x) = zeroR) /\
      (!x y. mulR x y = mulR y x) /\
      (!x y z. mulR (mulR x y) z = mulR x (mulR y z)) /\
      (!x. mulR x oneR = x) /\
      (!a x y. mulR a (addR x y) = addR (mulR a x) (mulR a y))``);

val babel_vspace_def = new_definition (
  "babel_vspace_def",
  ``babel_vspace (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (oppV : 'v -> 'v)
      (smul : 'r -> 'v -> 'v) <=>
      (!u v. addV u v = addV v u) /\
      (!u v w. addV (addV u v) w = addV u (addV v w)) /\
      (!u. addV u zeroV = u) /\
      (!u. addV u (oppV u) = zeroV) /\
      (!a u v. smul a (addV u v) = addV (smul a u) (smul a v)) /\
      (!a b u. smul (addR a b) u = addV (smul a u) (smul b u)) /\
      (!a b u. smul (mulR a b) u = smul a (smul b u)) /\
      (!u. smul oneR u = u) /\
      (!a. smul a zeroV = zeroV)``);

val babel_linear_map_def = new_definition (
  "babel_linear_map_def",
  ``babel_linear_map
      (addV : 'v -> 'v -> 'v) (smulV : 'r -> 'v -> 'v)
      (addW : 'w -> 'w -> 'w) (smulW : 'r -> 'w -> 'w)
      (toFun : 'v -> 'w) <=>
      (!u v. toFun (addV u v) = addW (toFun u) (toFun v)) /\
      (!a u. toFun (smulV a u) = smulW a (toFun u))``);

val babel_linear_map_context_def = new_definition (
  "babel_linear_map_context_def",
  ``babel_linear_map_context
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (oppV : 'v -> 'v)
      (smulV : 'r -> 'v -> 'v)
      (zeroW : 'w) (addW : 'w -> 'w -> 'w) (oppW : 'w -> 'w)
      (smulW : 'r -> 'w -> 'w) (toFun : 'v -> 'w) <=>
      babel_field zeroR oneR addR mulR oppR /\
      babel_vspace oneR addR mulR zeroV addV oppV smulV /\
      babel_vspace oneR addR mulR zeroW addW oppW smulW /\
      babel_linear_map addV smulV addW smulW toFun``);

val babel_ker_def = new_definition (
  "babel_ker_def",
  ``babel_ker (toFun : 'v -> 'w) (zeroW : 'w) x <=>
      toFun x = zeroW``);

val babel_im_def = new_definition (
  "babel_im_def",
  ``babel_im (toFun : 'v -> 'w) y <=>
      ?x. toFun x = y``);

val ker_add =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (oppV : 'v -> 'v)
      (smulV : 'r -> 'v -> 'v)
      (zeroW : 'w) (addW : 'w -> 'w -> 'w) (oppW : 'w -> 'w)
      (smulW : 'r -> 'w -> 'w) (toFun : 'v -> 'w).
      babel_linear_map_context zeroR oneR addR mulR oppR
        zeroV addV oppV smulV zeroW addW oppW smulW toFun ==>
      !x y.
        babel_ker toFun zeroW x ==>
        babel_ker toFun zeroW y ==>
        babel_ker toFun zeroW (addV x y)``;

val ker_smul =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (oppV : 'v -> 'v)
      (smulV : 'r -> 'v -> 'v)
      (zeroW : 'w) (addW : 'w -> 'w -> 'w) (oppW : 'w -> 'w)
      (smulW : 'r -> 'w -> 'w) (toFun : 'v -> 'w).
      babel_linear_map_context zeroR oneR addR mulR oppR
        zeroV addV oppV smulV zeroW addW oppW smulW toFun ==>
      !a x.
        babel_ker toFun zeroW x ==>
        babel_ker toFun zeroW (smulV a x)``;

val im_add =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (oppV : 'v -> 'v)
      (smulV : 'r -> 'v -> 'v)
      (zeroW : 'w) (addW : 'w -> 'w -> 'w) (oppW : 'w -> 'w)
      (smulW : 'r -> 'w -> 'w) (toFun : 'v -> 'w).
      babel_linear_map_context zeroR oneR addR mulR oppR
        zeroV addV oppV smulV zeroW addW oppW smulW toFun ==>
      !y z.
        babel_im toFun y ==>
        babel_im toFun z ==>
        babel_im toFun (addW y z)``;

val im_smul =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (oppV : 'v -> 'v)
      (smulV : 'r -> 'v -> 'v)
      (zeroW : 'w) (addW : 'w -> 'w -> 'w) (oppW : 'w -> 'w)
      (smulW : 'r -> 'w -> 'w) (toFun : 'v -> 'w).
      babel_linear_map_context zeroR oneR addR mulR oppR
        zeroV addV oppV smulV zeroW addW oppW smulW toFun ==>
      !a y.
        babel_im toFun y ==>
        babel_im toFun (smulW a y)``;

val _ = export_theory();
