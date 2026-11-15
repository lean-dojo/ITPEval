(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q4878586, "Beck's monadicity theorem": a right adjoint that creates
  coequalizers of all pairs split by the right adjoint is monadic.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val q4878586_category_def = new_definition (
  "q4878586_category_def",
  ``q4878586_category
      (objects : 'o set) (morphisms : 'm set)
      (dom : 'm -> 'o) (cod : 'm -> 'o)
      (id : 'o -> 'm) (comp : 'm -> 'm -> 'm) <=>
      (!f. f IN morphisms ==> dom f IN objects /\ cod f IN objects) /\
      (!x. x IN objects ==>
        id x IN morphisms /\ dom (id x) = x /\ cod (id x) = x) /\
      (!f g.
        f IN morphisms /\ g IN morphisms /\ cod f = dom g
        ==>
        comp g f IN morphisms /\
        dom (comp g f) = dom f /\
        cod (comp g f) = cod g) /\
      (!f. f IN morphisms ==>
        comp f (id (dom f)) = f /\
        comp (id (cod f)) f = f) /\
      (!f g h.
        f IN morphisms /\ g IN morphisms /\ h IN morphisms /\
        cod f = dom g /\ cod g = dom h
        ==>
        comp h (comp g f) = comp (comp h g) f)``);

val q4878586_functor_def = new_definition (
  "q4878586_functor_def",
  ``q4878586_functor
      (src_objects : 'o1 set) (src_morphisms : 'm1 set)
      (src_dom : 'm1 -> 'o1) (src_cod : 'm1 -> 'o1)
      (src_id : 'o1 -> 'm1) (src_comp : 'm1 -> 'm1 -> 'm1)
      (dst_objects : 'o2 set) (dst_morphisms : 'm2 set)
      (dst_dom : 'm2 -> 'o2) (dst_cod : 'm2 -> 'o2)
      (dst_id : 'o2 -> 'm2) (dst_comp : 'm2 -> 'm2 -> 'm2)
      (obj_map : 'o1 -> 'o2) (mor_map : 'm1 -> 'm2) <=>
      (!x. x IN src_objects ==> obj_map x IN dst_objects) /\
      (!f. f IN src_morphisms ==>
        mor_map f IN dst_morphisms /\
        dst_dom (mor_map f) = obj_map (src_dom f) /\
        dst_cod (mor_map f) = obj_map (src_cod f)) /\
      (!x. x IN src_objects ==>
        mor_map (src_id x) = dst_id (obj_map x)) /\
      (!f g.
        f IN src_morphisms /\ g IN src_morphisms /\
        src_cod f = src_dom g
        ==>
        mor_map (src_comp g f) = dst_comp (mor_map g) (mor_map f))``);

val q4878586_adjunction_def = new_definition (
  "q4878586_adjunction_def",
  ``q4878586_adjunction
      (cobjects : 'co set) (cmorphisms : 'cm set)
      (cdom : 'cm -> 'co) (ccod : 'cm -> 'co)
      (cid : 'co -> 'cm) (ccomp : 'cm -> 'cm -> 'cm)
      (dobjects : 'do set) (dmorphisms : 'dm set)
      (ddom : 'dm -> 'do) (dcod : 'dm -> 'do)
      (did : 'do -> 'dm) (dcomp : 'dm -> 'dm -> 'dm)
      (fobj : 'co -> 'do) (fmap : 'cm -> 'dm)
      (gobj : 'do -> 'co) (gmap : 'dm -> 'cm)
      (unit : 'co -> 'cm) (counit : 'do -> 'dm) <=>
      (!x. x IN cobjects ==>
        unit x IN cmorphisms /\
        cdom (unit x) = x /\
        ccod (unit x) = gobj (fobj x)) /\
      (!h. h IN cmorphisms ==>
        ccomp (gmap (fmap h)) (unit (cdom h)) =
          ccomp (unit (ccod h)) h) /\
      (!y. y IN dobjects ==>
        counit y IN dmorphisms /\
        ddom (counit y) = fobj (gobj y) /\
        dcod (counit y) = y) /\
      (!h. h IN dmorphisms ==>
        dcomp (counit (dcod h)) (fmap (gmap h)) =
          dcomp h (counit (ddom h))) /\
      (!x. x IN cobjects ==>
        dcomp (counit (fobj x)) (fmap (unit x)) = did (fobj x)) /\
      (!y. y IN dobjects ==>
        ccomp (gmap (counit y)) (unit (gobj y)) = cid (gobj y))``);

val q4878586_parallel_def = new_definition (
  "q4878586_parallel_def",
  ``q4878586_parallel
      (morphisms : 'm set) (dom : 'm -> 'o) (cod : 'm -> 'o)
      (f : 'm) (g : 'm) <=>
      f IN morphisms /\ g IN morphisms /\
      dom f = dom g /\ cod f = cod g``);

val q4878586_coequalizer_def = new_definition (
  "q4878586_coequalizer_def",
  ``q4878586_coequalizer
      (objects : 'o set) (morphisms : 'm set)
      (dom : 'm -> 'o) (cod : 'm -> 'o)
      (comp : 'm -> 'm -> 'm)
      (f : 'm) (g : 'm) (q : 'm) <=>
      q4878586_parallel morphisms dom cod f g /\
      q IN morphisms /\ dom q = cod f /\
      comp q f = comp q g /\
      !w h.
        w IN objects /\ h IN morphisms /\
        dom h = cod f /\ cod h = w /\
        comp h f = comp h g
        ==>
        ?u. u IN morphisms /\
            dom u = cod q /\ cod u = w /\
            comp u q = h /\
            !v. v IN morphisms /\
                dom v = cod q /\ cod v = w /\
                comp v q = h
                ==> v = u``);

val q4878586_g_split_pair_def = new_definition (
  "q4878586_g_split_pair_def",
  ``q4878586_g_split_pair
      (cobjects : 'co set) (cmorphisms : 'cm set)
      (cdom : 'cm -> 'co) (ccod : 'cm -> 'co)
      (cid : 'co -> 'cm) (ccomp : 'cm -> 'cm -> 'cm)
      (dmorphisms : 'dm set)
      (ddom : 'dm -> 'do) (dcod : 'dm -> 'do)
      (gobj : 'do -> 'co) (gmap : 'dm -> 'cm)
      (f : 'dm) (g : 'dm) <=>
      q4878586_parallel dmorphisms ddom dcod f g /\
      ?z q s t.
        z IN cobjects /\
        q IN cmorphisms /\
        cdom q = gobj (dcod f) /\ ccod q = z /\
        s IN cmorphisms /\
        cdom s = z /\ ccod s = gobj (dcod f) /\
        t IN cmorphisms /\
        cdom t = gobj (dcod f) /\ ccod t = gobj (ddom f) /\
        ccomp q (gmap f) = ccomp q (gmap g) /\
        ccomp q s = cid z /\
        ccomp (gmap g) t = cid (gobj (dcod f)) /\
        ccomp (gmap f) t = ccomp s q``);

val q4878586_creates_coequalizer_def = new_definition (
  "q4878586_creates_coequalizer_def",
  ``q4878586_creates_coequalizer
      (cobjects : 'co set) (cmorphisms : 'cm set)
      (cdom : 'cm -> 'co) (ccod : 'cm -> 'co)
      (cid : 'co -> 'cm) (ccomp : 'cm -> 'cm -> 'cm)
      (dobjects : 'do set) (dmorphisms : 'dm set)
      (ddom : 'dm -> 'do) (dcod : 'dm -> 'do)
      (dcomp : 'dm -> 'dm -> 'dm)
      (gobj : 'do -> 'co) (gmap : 'dm -> 'cm)
      (f : 'dm) (g : 'dm) <=>
      (!q.
        q IN dmorphisms /\ ddom q = dcod f /\
        dcomp q f = dcomp q g /\
        q4878586_coequalizer
          cobjects cmorphisms cdom ccod ccomp
          (gmap f) (gmap g) (gmap q)
        ==>
        q4878586_coequalizer
          dobjects dmorphisms ddom dcod dcomp f g q) /\
      (!q.
        q4878586_coequalizer
          cobjects cmorphisms cdom ccod ccomp
          (gmap f) (gmap g) q
        ==>
        ?w r i j.
          w IN dobjects /\
          r IN dmorphisms /\
          ddom r = dcod f /\ dcod r = w /\
          dcomp r f = dcomp r g /\
          i IN cmorphisms /\
          cdom i = gobj w /\ ccod i = ccod q /\
          j IN cmorphisms /\
          cdom j = ccod q /\ ccod j = gobj w /\
          ccomp j i = cid (gobj w) /\
          ccomp i j = cid (ccod q) /\
          ccomp i (gmap r) = q)``);

val q4878586_creates_g_split_coequalizers_def = new_definition (
  "q4878586_creates_g_split_coequalizers_def",
  ``q4878586_creates_g_split_coequalizers
      (cobjects : 'co set) (cmorphisms : 'cm set)
      (cdom : 'cm -> 'co) (ccod : 'cm -> 'co)
      (cid : 'co -> 'cm) (ccomp : 'cm -> 'cm -> 'cm)
      (dobjects : 'do set) (dmorphisms : 'dm set)
      (ddom : 'dm -> 'do) (dcod : 'dm -> 'do)
      (dcomp : 'dm -> 'dm -> 'dm)
      (gobj : 'do -> 'co) (gmap : 'dm -> 'cm) <=>
      !f g.
        q4878586_g_split_pair
          cobjects cmorphisms cdom ccod cid ccomp
          dmorphisms ddom dcod gobj gmap f g
        ==>
        q4878586_creates_coequalizer
          cobjects cmorphisms cdom ccod cid ccomp
          dobjects dmorphisms ddom dcod dcomp
          gobj gmap f g``);

val q4878586_algebra_def = new_definition (
  "q4878586_algebra_def",
  ``q4878586_algebra
      (cobjects : 'co set) (cmorphisms : 'cm set)
      (cdom : 'cm -> 'co) (ccod : 'cm -> 'co)
      (cid : 'co -> 'cm) (ccomp : 'cm -> 'cm -> 'cm)
      (fobj : 'co -> 'do) (fmap : 'cm -> 'dm)
      (gobj : 'do -> 'co) (gmap : 'dm -> 'cm)
      (unit : 'co -> 'cm) (counit : 'do -> 'dm)
      (aobj : 'co) (action : 'cm) <=>
      aobj IN cobjects /\
      action IN cmorphisms /\
      cdom action = gobj (fobj aobj) /\
      ccod action = aobj /\
      ccomp action (unit aobj) = cid aobj /\
      ccomp action (gmap (counit (fobj aobj))) =
        ccomp action (gmap (fmap action))``);

val q4878586_algebra_hom_def = new_definition (
  "q4878586_algebra_hom_def",
  ``q4878586_algebra_hom
      (cmorphisms : 'cm set)
      (cdom : 'cm -> 'co) (ccod : 'cm -> 'co)
      (ccomp : 'cm -> 'cm -> 'cm)
      (fmap : 'cm -> 'dm) (gmap : 'dm -> 'cm)
      (aobj : 'co) (action_a : 'cm)
      (bobj : 'co) (action_b : 'cm) (h : 'cm) <=>
      h IN cmorphisms /\
      cdom h = aobj /\ ccod h = bobj /\
      ccomp action_b (gmap (fmap h)) =
        ccomp h action_a``);

val q4878586_algebra_iso_def = new_definition (
  "q4878586_algebra_iso_def",
  ``q4878586_algebra_iso
      (cmorphisms : 'cm set)
      (cdom : 'cm -> 'co) (ccod : 'cm -> 'co)
      (cid : 'co -> 'cm) (ccomp : 'cm -> 'cm -> 'cm)
      (fmap : 'cm -> 'dm) (gmap : 'dm -> 'cm)
      (aobj : 'co) (action_a : 'cm)
      (bobj : 'co) (action_b : 'cm) <=>
      ?h k.
        q4878586_algebra_hom
          cmorphisms cdom ccod ccomp fmap gmap
          aobj action_a bobj action_b h /\
        q4878586_algebra_hom
          cmorphisms cdom ccod ccomp fmap gmap
          bobj action_b aobj action_a k /\
        ccomp k h = cid aobj /\
        ccomp h k = cid bobj``);

val q4878586_comparison_equivalence_def = new_definition (
  "q4878586_comparison_equivalence_def",
  ``q4878586_comparison_equivalence
      (cobjects : 'co set) (cmorphisms : 'cm set)
      (cdom : 'cm -> 'co) (ccod : 'cm -> 'co)
      (cid : 'co -> 'cm) (ccomp : 'cm -> 'cm -> 'cm)
      (dobjects : 'do set) (dmorphisms : 'dm set)
      (ddom : 'dm -> 'do) (dcod : 'dm -> 'do)
      (fobj : 'co -> 'do) (fmap : 'cm -> 'dm)
      (gobj : 'do -> 'co) (gmap : 'dm -> 'cm)
      (unit : 'co -> 'cm) (counit : 'do -> 'dm) <=>
      (!x y h k.
        x IN dobjects /\ y IN dobjects /\
        h IN dmorphisms /\ k IN dmorphisms /\
        ddom h = x /\ dcod h = y /\
        ddom k = x /\ dcod k = y /\
        gmap h = gmap k
        ==> h = k) /\
      (!x y h.
        x IN dobjects /\ y IN dobjects /\
        q4878586_algebra_hom
          cmorphisms cdom ccod ccomp fmap gmap
          (gobj x) (gmap (counit x))
          (gobj y) (gmap (counit y)) h
        ==>
        ?k. k IN dmorphisms /\
            ddom k = x /\ dcod k = y /\
            gmap k = h) /\
      (!aobj action.
        q4878586_algebra
          cobjects cmorphisms cdom ccod cid ccomp
          fobj fmap gobj gmap unit counit aobj action
        ==>
        ?x. x IN dobjects /\
            q4878586_algebra_iso
              cmorphisms cdom ccod cid ccomp fmap gmap
              (gobj x) (gmap (counit x)) aobj action)``);

val q4878586_monadic_right_adjoint_def = new_definition (
  "q4878586_monadic_right_adjoint_def",
  ``q4878586_monadic_right_adjoint
      (cobjects : 'co set) (cmorphisms : 'cm set)
      (cdom : 'cm -> 'co) (ccod : 'cm -> 'co)
      (cid : 'co -> 'cm) (ccomp : 'cm -> 'cm -> 'cm)
      (dobjects : 'do set) (dmorphisms : 'dm set)
      (ddom : 'dm -> 'do) (dcod : 'dm -> 'do)
      (did : 'do -> 'dm) (dcomp : 'dm -> 'dm -> 'dm)
      (gobj : 'do -> 'co) (gmap : 'dm -> 'cm) <=>
      ?(fobj : 'co -> 'do) (fmap : 'cm -> 'dm)
       (unit : 'co -> 'cm) (counit : 'do -> 'dm).
        q4878586_functor
          cobjects cmorphisms cdom ccod cid ccomp
          dobjects dmorphisms ddom dcod did dcomp
          fobj fmap /\
        q4878586_adjunction
          cobjects cmorphisms cdom ccod cid ccomp
          dobjects dmorphisms ddom dcod did dcomp
          fobj fmap gobj gmap unit counit /\
        q4878586_comparison_equivalence
          cobjects cmorphisms cdom ccod cid ccomp
          dobjects dmorphisms ddom dcod
          fobj fmap gobj gmap unit counit``);

val becks_monadicity_theorem =
  ``!(cobjects : 'co set) (cmorphisms : 'cm set)
      (cdom : 'cm -> 'co) (ccod : 'cm -> 'co)
      (cid : 'co -> 'cm) (ccomp : 'cm -> 'cm -> 'cm)
      (dobjects : 'do set) (dmorphisms : 'dm set)
      (ddom : 'dm -> 'do) (dcod : 'dm -> 'do)
      (did : 'do -> 'dm) (dcomp : 'dm -> 'dm -> 'dm)
      (fobj : 'co -> 'do) (fmap : 'cm -> 'dm)
      (gobj : 'do -> 'co) (gmap : 'dm -> 'cm)
      (unit : 'co -> 'cm) (counit : 'do -> 'dm).
      q4878586_category
        cobjects cmorphisms cdom ccod cid ccomp /\
      q4878586_category
        dobjects dmorphisms ddom dcod did dcomp /\
      q4878586_functor
        cobjects cmorphisms cdom ccod cid ccomp
        dobjects dmorphisms ddom dcod did dcomp
        fobj fmap /\
      q4878586_functor
        dobjects dmorphisms ddom dcod did dcomp
        cobjects cmorphisms cdom ccod cid ccomp
        gobj gmap /\
      q4878586_adjunction
        cobjects cmorphisms cdom ccod cid ccomp
        dobjects dmorphisms ddom dcod did dcomp
        fobj fmap gobj gmap unit counit /\
      q4878586_creates_g_split_coequalizers
        cobjects cmorphisms cdom ccod cid ccomp
        dobjects dmorphisms ddom dcod dcomp
        gobj gmap
      ==>
      q4878586_monadic_right_adjoint
        cobjects cmorphisms cdom ccod cid ccomp
        dobjects dmorphisms ddom dcod did dcomp
        gobj gmap``;
