(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q8066795 (thousand-theorems__hol4__Q8066795), "Zariski's main theorem":
  a proper morphism of schemes with a finite fiber over a point is finite
  over an open neighborhood of that point. Schemes, scheme morphisms,
  properness, finiteness, open subschemes, and restrictions use complete
  extensional encodings below. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory topologyTheory arithmeticTheory;

val q8066795_comm_ring_def = new_definition (
  "q8066795_comm_ring_def",
  ``q8066795_comm_ring
      (carrier : 'a set) (z : 'a) (u : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (pow : 'a -> num -> 'a) <=>
      z IN carrier /\ u IN carrier /\
      (!a b. a IN carrier /\ b IN carrier ==>
        add a b IN carrier /\ mul a b IN carrier) /\
      (!a. a IN carrier ==> neg a IN carrier) /\
      (!a b c. a IN carrier /\ b IN carrier /\ c IN carrier ==>
        add (add a b) c = add a (add b c) /\
        mul (mul a b) c = mul a (mul b c)) /\
      (!a b. a IN carrier /\ b IN carrier ==>
        add a b = add b a /\ mul a b = mul b a) /\
      (!a. a IN carrier ==>
        add z a = a /\ mul u a = a /\ add (neg a) a = z) /\
      (!a b c. a IN carrier /\ b IN carrier /\ c IN carrier ==>
        mul a (add b c) = add (mul a b) (mul a c)) /\
      (!a. a IN carrier ==>
        pow a 0 = u /\ (!n. pow a (SUC n) = mul a (pow a n)))``);

val q8066795_ring_hom_def = new_definition (
  "q8066795_ring_hom_def",
  ``q8066795_ring_hom
      (ring_a : 'a set) (zA : 'a) (oA : 'a)
      (addA : 'a -> 'a -> 'a) (mulA : 'a -> 'a -> 'a)
      (negA : 'a -> 'a) (powA : 'a -> num -> 'a)
      (ring_b : 'a set) (zB : 'a) (oB : 'a)
      (addB : 'a -> 'a -> 'a) (mulB : 'a -> 'a -> 'a)
      (negB : 'a -> 'a) (powB : 'a -> num -> 'a)
      (phi : 'a -> 'a) <=>
      q8066795_comm_ring ring_a zA oA addA mulA negA powA /\
      q8066795_comm_ring ring_b zB oB addB mulB negB powB /\
      (!a. a IN ring_a ==> phi a IN ring_b) /\
      phi zA = zB /\ phi oA = oB /\
      (!a b. a IN ring_a /\ b IN ring_a ==>
        phi (addA a b) = addB (phi a) (phi b) /\
        phi (mulA a b) = mulB (phi a) (phi b) /\
        phi (negA a) = negB (phi a) /\
        (!n. phi (powA a n) = powB (phi a) n))``);

val q8066795_germ_eq_def = new_definition (
  "q8066795_germ_eq_def",
  ``q8066795_germ_eq
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (sections : 's -> 'p set -> 'a set)
      (res : 's -> 'p set -> 'p set -> 'a -> 'a)
      (sch : 's) (x : 'p) (u_open : 'p set) (a : 'a)
      (v_open : 'p set) (b : 'a) <=>
      x IN u_open /\ x IN v_open /\ a IN sections sch u_open /\ b IN sections sch v_open /\
      ?w_open. open_in (top sch) w_open /\ x IN w_open /\ w_open SUBSET u_open INTER v_open /\
          res sch u_open w_open a = res sch v_open w_open b``);

val q8066795_germ_unit_def = new_definition (
  "q8066795_germ_unit_def",
  ``q8066795_germ_unit
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (sections : 's -> 'p set -> 'a set)
      (ring_one : 's -> 'p set -> 'a)
      (mul : 's -> 'p set -> 'a -> 'a -> 'a)
      (res : 's -> 'p set -> 'p set -> 'a -> 'a)
      (sch : 's) (x : 'p) (u_open : 'p set) (a : 'a) <=>
      x IN u_open /\ a IN sections sch u_open /\
      ?v_open b c.
        open_in (top sch) v_open /\ x IN v_open /\ v_open SUBSET u_open /\
        b IN sections sch v_open /\ c IN sections sch v_open /\
        q8066795_germ_eq pts top sections res sch x u_open a v_open b /\
        mul sch v_open b c = ring_one sch v_open``);

val q8066795_prime_ideal_def = new_definition (
  "q8066795_prime_ideal_def",
  ``q8066795_prime_ideal
      (ring_a : 'a set) (z : 'a) (u : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (ideal : 'a set) <=>
      ideal SUBSET ring_a /\ z IN ideal /\ ~(u IN ideal) /\
      (!a. a IN ideal ==> neg a IN ideal) /\
      (!a b. a IN ideal /\ b IN ideal ==> add a b IN ideal) /\
      (!a b. a IN ring_a /\ b IN ideal ==> mul a b IN ideal) /\
      (!a b. a IN ring_a /\ b IN ring_a /\ mul a b IN ideal ==>
        a IN ideal \/ b IN ideal)``);

val q8066795_sheaf_of_local_rings_def = new_definition (
  "q8066795_sheaf_of_local_rings_def",
  ``q8066795_sheaf_of_local_rings
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (sections : 's -> 'p set -> 'a set)
      (zero : 's -> 'p set -> 'a) (ring_one : 's -> 'p set -> 'a)
      (add : 's -> 'p set -> 'a -> 'a -> 'a)
      (mul : 's -> 'p set -> 'a -> 'a -> 'a)
      (neg : 's -> 'p set -> 'a -> 'a)
      (pow : 's -> 'p set -> 'a -> num -> 'a)
      (res : 's -> 'p set -> 'p set -> 'a -> 'a)
      (sch : 's) <=>
      topspace (top sch) = pts sch /\
      (!u_open. open_in (top sch) u_open ==>
        q8066795_comm_ring
          (sections sch u_open) (zero sch u_open) (ring_one sch u_open)
          (add sch u_open) (mul sch u_open) (neg sch u_open) (pow sch u_open)) /\
      (!u_open v_open. open_in (top sch) u_open /\ open_in (top sch) v_open /\ v_open SUBSET u_open ==>
        q8066795_ring_hom
          (sections sch u_open) (zero sch u_open) (ring_one sch u_open)
          (add sch u_open) (mul sch u_open) (neg sch u_open) (pow sch u_open)
          (sections sch v_open) (zero sch v_open) (ring_one sch v_open)
          (add sch v_open) (mul sch v_open) (neg sch v_open) (pow sch v_open)
          (res sch u_open v_open)) /\
      (!u_open a. open_in (top sch) u_open /\ a IN sections sch u_open ==>
        res sch u_open u_open a = a) /\
      (!u_open v_open w_open a.
        open_in (top sch) u_open /\ open_in (top sch) v_open /\
        open_in (top sch) w_open /\ w_open SUBSET v_open /\ v_open SUBSET u_open /\
        a IN sections sch u_open ==>
        res sch v_open w_open (res sch u_open v_open a) = res sch u_open w_open a) /\
      (!u_open (cover : ('p set) set) (family : 'p set -> 'a).
        open_in (top sch) u_open /\
        (!v_open. v_open IN cover ==> open_in (top sch) v_open /\ v_open SUBSET u_open) /\
        BIGUNION cover = u_open /\
        (!v_open. v_open IN cover ==> family v_open IN sections sch v_open) /\
        (!v_open w_open. v_open IN cover /\ w_open IN cover ==>
          res sch v_open (v_open INTER w_open) (family v_open) =
          res sch w_open (v_open INTER w_open) (family w_open))
        ==>
        ?!a. a IN sections sch u_open /\
          !v_open. v_open IN cover ==> res sch u_open v_open a = family v_open) /\
      (!x u_open a.
        x IN pts sch /\ open_in (top sch) u_open /\ x IN u_open /\ a IN sections sch u_open
        ==>
        q8066795_germ_unit pts top sections ring_one mul res sch x u_open a \/
        q8066795_germ_unit pts top sections ring_one mul res sch x u_open
          (add sch u_open (ring_one sch u_open) (neg sch u_open a)))``);

val q8066795_affine_open_def = new_definition (
  "q8066795_affine_open_def",
  ``q8066795_affine_open
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (sections : 's -> 'p set -> 'a set)
      (zero : 's -> 'p set -> 'a) (ring_one : 's -> 'p set -> 'a)
      (add : 's -> 'p set -> 'a -> 'a -> 'a)
      (mul : 's -> 'p set -> 'a -> 'a -> 'a)
      (neg : 's -> 'p set -> 'a -> 'a)
      (pow : 's -> 'p set -> 'a -> num -> 'a)
      (res : 's -> 'p set -> 'p set -> 'a -> 'a)
      (sch : 's) (u_open : 'p set) <=>
      open_in (top sch) u_open /\
      let prime_at =
        \x. {a | a IN sections sch u_open /\
                 ~q8066795_germ_unit pts top sections ring_one mul res sch x u_open a};
          basic =
        \a. {x | x IN u_open /\
                 q8066795_germ_unit pts top sections ring_one mul res sch x u_open a}
      in
        BIJ prime_at u_open
          {ideal | q8066795_prime_ideal
                 (sections sch u_open) (zero sch u_open) (ring_one sch u_open)
                 (add sch u_open) (mul sch u_open) (neg sch u_open) ideal} /\
        (!a. a IN sections sch u_open ==>
          basic a = {x | x IN u_open /\ ~(a IN prime_at x)}) /\
        (!w_open. w_open SUBSET u_open ==>
          (open_in (top sch) w_open <=>
           !x. x IN w_open ==> ?a.
             a IN sections sch u_open /\ x IN basic a /\ basic a SUBSET w_open)) /\
        (!a. a IN sections sch u_open ==>
          open_in (top sch) (basic a) /\
          q8066795_ring_hom
            (sections sch u_open) (zero sch u_open) (ring_one sch u_open)
            (add sch u_open) (mul sch u_open) (neg sch u_open) (pow sch u_open)
            (sections sch (basic a)) (zero sch (basic a)) (ring_one sch (basic a))
            (add sch (basic a)) (mul sch (basic a))
            (neg sch (basic a)) (pow sch (basic a))
            (res sch u_open (basic a)) /\
          (!t. t IN sections sch (basic a) ==> ?b n.
            b IN sections sch u_open /\
            mul sch (basic a) t
              (res sch u_open (basic a) (pow sch u_open a n)) =
            res sch u_open (basic a) b) /\
          (!b c. b IN sections sch u_open /\ c IN sections sch u_open ==>
            (res sch u_open (basic a) b = res sch u_open (basic a) c <=>
             ?n. mul sch u_open (pow sch u_open a n)
                   (add sch u_open b (neg sch u_open c)) = zero sch u_open)))``);

val q8066795_scheme_def = new_definition (
  "q8066795_scheme_def",
  ``q8066795_scheme
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (sections : 's -> 'p set -> 'a set)
      (zero : 's -> 'p set -> 'a) (ring_one : 's -> 'p set -> 'a)
      (add : 's -> 'p set -> 'a -> 'a -> 'a)
      (mul : 's -> 'p set -> 'a -> 'a -> 'a)
      (neg : 's -> 'p set -> 'a -> 'a)
      (pow : 's -> 'p set -> 'a -> num -> 'a)
      (res : 's -> 'p set -> 'p set -> 'a -> 'a)
      (sch : 's) <=>
      q8066795_sheaf_of_local_rings
        pts top sections zero ring_one add mul neg pow res sch /\
      !x. x IN pts sch ==> ?u_open.
        x IN u_open /\
        q8066795_affine_open
          pts top sections zero ring_one add mul neg pow res sch u_open``);

val q8066795_scheme_morphism_def = new_definition (
  "q8066795_scheme_morphism_def",
  ``q8066795_scheme_morphism
      (schemes : 's set)
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (sections : 's -> 'p set -> 'a set)
      (zero : 's -> 'p set -> 'a) (ring_one : 's -> 'p set -> 'a)
      (add : 's -> 'p set -> 'a -> 'a -> 'a)
      (mul : 's -> 'p set -> 'a -> 'a -> 'a)
      (neg : 's -> 'p set -> 'a -> 'a)
      (pow : 's -> 'p set -> 'a -> num -> 'a)
      (res : 's -> 'p set -> 'p set -> 'a -> 'a)
      (source : 's) (target : 's)
      (point_map : 'p -> 'p)
      (section_map : 'p set -> 'a -> 'a) <=>
      source IN schemes /\ target IN schemes /\
      q8066795_scheme pts top sections zero ring_one add mul neg pow res source /\
      q8066795_scheme pts top sections zero ring_one add mul neg pow res target /\
      (!x. x IN pts source ==> point_map x IN pts target) /\
      (!u_open. open_in (top target) u_open ==>
        open_in (top source)
          (PREIMAGE point_map u_open INTER pts source) /\
        q8066795_ring_hom
          (sections target u_open) (zero target u_open) (ring_one target u_open)
          (add target u_open) (mul target u_open)
          (neg target u_open) (pow target u_open)
          (sections source (PREIMAGE point_map u_open INTER pts source))
          (zero source (PREIMAGE point_map u_open INTER pts source))
          (ring_one source (PREIMAGE point_map u_open INTER pts source))
          (add source (PREIMAGE point_map u_open INTER pts source))
          (mul source (PREIMAGE point_map u_open INTER pts source))
          (neg source (PREIMAGE point_map u_open INTER pts source))
          (pow source (PREIMAGE point_map u_open INTER pts source))
          (section_map u_open)) /\
      (!u_open v_open a.
        open_in (top target) u_open /\ open_in (top target) v_open /\
        v_open SUBSET u_open /\ a IN sections target u_open ==>
        res source
          (PREIMAGE point_map u_open INTER pts source)
          (PREIMAGE point_map v_open INTER pts source)
          (section_map u_open a) =
        section_map v_open (res target u_open v_open a)) /\
      (!x u_open a.
        x IN pts source /\ open_in (top target) u_open /\
        point_map x IN u_open /\ a IN sections target u_open ==>
        (q8066795_germ_unit pts top sections ring_one mul res
           target (point_map x) u_open a <=>
         q8066795_germ_unit pts top sections ring_one mul res
           source x
           (PREIMAGE point_map u_open INTER pts source)
           (section_map u_open a)))``);

val q8066795_module_finite_def = new_definition (
  "q8066795_module_finite_def",
  ``q8066795_module_finite
      (ring_b : 'a set) (zB : 'a) (oB : 'a)
      (addB : 'a -> 'a -> 'a) (mulB : 'a -> 'a -> 'a)
      (negB : 'a -> 'a) (powB : 'a -> num -> 'a)
      (ring_a : 'a set) (zA : 'a) (oA : 'a)
      (addA : 'a -> 'a -> 'a) (mulA : 'a -> 'a -> 'a)
      (negA : 'a -> 'a) (powA : 'a -> num -> 'a)
      (phi : 'a -> 'a) <=>
      q8066795_ring_hom
        ring_b zB oB addB mulB negB powB
        ring_a zA oA addA mulA negA powA phi /\
      ?generators. FINITE generators /\ generators SUBSET ring_a /\
        ring_a =
        INTERS {submodule |
          generators SUBSET submodule /\ zA IN submodule /\
          (!u. u IN submodule ==> negA u IN submodule) /\
          (!u v. u IN submodule /\ v IN submodule ==> addA u v IN submodule) /\
          (!b u. b IN ring_b /\ u IN submodule ==> mulA (phi b) u IN submodule)}``);

val q8066795_finite_type_def = new_definition (
  "q8066795_finite_type_def",
  ``q8066795_finite_type
      (ring_b : 'a set) (zB : 'a) (oB : 'a)
      (addB : 'a -> 'a -> 'a) (mulB : 'a -> 'a -> 'a)
      (negB : 'a -> 'a) (powB : 'a -> num -> 'a)
      (ring_a : 'a set) (zA : 'a) (oA : 'a)
      (addA : 'a -> 'a -> 'a) (mulA : 'a -> 'a -> 'a)
      (negA : 'a -> 'a) (powA : 'a -> num -> 'a)
      (phi : 'a -> 'a) <=>
      q8066795_ring_hom
        ring_b zB oB addB mulB negB powB
        ring_a zA oA addA mulA negA powA phi /\
      ?generators. FINITE generators /\ generators SUBSET ring_a /\
        ring_a =
        INTERS {subring |
          generators SUBSET subring /\ IMAGE phi ring_b SUBSET subring /\
          zA IN subring /\ oA IN subring /\
          (!u. u IN subring ==> negA u IN subring) /\
          (!u v. u IN subring /\ v IN subring ==>
            addA u v IN subring /\ mulA u v IN subring)}``);

val q8066795_closed_map_def = new_definition (
  "q8066795_closed_map_def",
  ``q8066795_closed_map
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (dom : 'm -> 's) (cod : 'm -> 's)
      (base : 'm -> 'p -> 'p) (m : 'm) <=>
      !closed_set. closed_in (top (dom m)) closed_set ==>
        closed_in (top (cod m)) (IMAGE (base m) closed_set)``);

val q8066795_closed_immersion_def = new_definition (
  "q8066795_closed_immersion_def",
  ``q8066795_closed_immersion
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (sections : 's -> 'p set -> 'a set)
      (res : 's -> 'p set -> 'p set -> 'a -> 'a)
      (dom : 'm -> 's) (cod : 'm -> 's)
      (base : 'm -> 'p -> 'p)
      (on_sec : 'm -> 'p set -> 'a -> 'a)
      (m : 'm) <=>
      INJ (base m) (pts (dom m)) (pts (cod m)) /\
      closed_in (top (cod m)) (IMAGE (base m) (pts (dom m))) /\
      (!ring_a. ring_a SUBSET pts (dom m) ==>
        (open_in (top (dom m)) ring_a <=>
         ?u_open. open_in (top (cod m)) u_open /\
             ring_a = PREIMAGE (base m) u_open INTER pts (dom m))) /\
      (!x u_open a.
        x IN pts (dom m) /\ open_in (top (dom m)) u_open /\
        x IN u_open /\ a IN sections (dom m) u_open ==>
        ?v_open b.
          open_in (top (cod m)) v_open /\ base m x IN v_open /\
          b IN sections (cod m) v_open /\
          q8066795_germ_eq pts top sections res
            (dom m) x u_open a
            (PREIMAGE (base m) v_open INTER pts (dom m))
            (on_sec m v_open b))``);

val q8066795_geometry_def = new_definition (
  "q8066795_geometry_def",
  ``q8066795_geometry
      (schemes : 's set) (morphisms : 'm set)
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (sections : 's -> 'p set -> 'a set)
      (zero : 's -> 'p set -> 'a) (ring_one : 's -> 'p set -> 'a)
      (add : 's -> 'p set -> 'a -> 'a -> 'a)
      (mul : 's -> 'p set -> 'a -> 'a -> 'a)
      (neg : 's -> 'p set -> 'a -> 'a)
      (pow : 's -> 'p set -> 'a -> num -> 'a)
      (res : 's -> 'p set -> 'p set -> 'a -> 'a)
      (dom : 'm -> 's) (cod : 'm -> 's)
      (base : 'm -> 'p -> 'p)
      (on_sec : 'm -> 'p set -> 'a -> 'a)
      (id_mor : 's -> 'm) (comp : 'm -> 'm -> 'm)
      (open_obj : 's -> 'p set -> 's)
      (open_inclusion : 's -> 'p set -> 'm)
      (restrict : 'm -> 'p set -> 'm)
      (pullback_obj : 'm -> 'm -> 's)
      (pullback_fst : 'm -> 'm -> 'm)
      (pullback_snd : 'm -> 'm -> 'm)
      (pullback_lift : 'm -> 'm -> 'm -> 'm -> 'm)
      (diagonal : 'm -> 'm) <=>
      (!sch. sch IN schemes <=>
        q8066795_scheme pts top sections zero ring_one add mul neg pow res sch) /\
      (!raw_pts raw_top raw_sections raw_zero raw_one
         raw_add raw_mul raw_neg raw_pow raw_res (raw_sch : 's).
        q8066795_scheme
          raw_pts raw_top raw_sections raw_zero raw_one
          raw_add raw_mul raw_neg raw_pow raw_res raw_sch
        ==>
        ?sch. sch IN schemes /\
          pts sch = raw_pts raw_sch /\
          top sch = raw_top raw_sch /\
          sections sch = raw_sections raw_sch /\
          zero sch = raw_zero raw_sch /\
          ring_one sch = raw_one raw_sch /\
          add sch = raw_add raw_sch /\
          mul sch = raw_mul raw_sch /\
          neg sch = raw_neg raw_sch /\
          pow sch = raw_pow raw_sch /\
          res sch = raw_res raw_sch) /\
      (!sch1 sch2.
        sch1 IN schemes /\ sch2 IN schemes /\
        pts sch1 = pts sch2 /\ top sch1 = top sch2 /\
        sections sch1 = sections sch2 /\
        zero sch1 = zero sch2 /\ ring_one sch1 = ring_one sch2 /\
        add sch1 = add sch2 /\ mul sch1 = mul sch2 /\
        neg sch1 = neg sch2 /\ pow sch1 = pow sch2 /\
        res sch1 = res sch2
        ==>
        sch1 = sch2) /\
      (!m. m IN morphisms <=>
        q8066795_scheme_morphism
          schemes pts top sections zero ring_one add mul neg pow res
          (dom m) (cod m) (base m) (on_sec m)) /\
      (!source target point_map section_map.
        q8066795_scheme_morphism
          schemes pts top sections zero ring_one add mul neg pow res
          source target point_map section_map
        ==>
        ?m. m IN morphisms /\ dom m = source /\ cod m = target /\
          (!x. x IN pts source ==> base m x = point_map x) /\
          (!u_open a.
            open_in (top target) u_open /\ a IN sections target u_open ==>
            on_sec m u_open a = section_map u_open a)) /\
      (!f g.
        f IN morphisms /\ g IN morphisms /\
        dom f = dom g /\ cod f = cod g /\
        (!x. x IN pts (dom f) ==> base f x = base g x) /\
        (!u_open a.
          open_in (top (cod f)) u_open /\ a IN sections (cod f) u_open ==>
          on_sec f u_open a = on_sec g u_open a)
        ==>
        f = g) /\
      (!sch. sch IN schemes ==>
        id_mor sch IN morphisms /\
        dom (id_mor sch) = sch /\ cod (id_mor sch) = sch /\
        (!x. x IN pts sch ==> base (id_mor sch) x = x) /\
        (!u_open a. open_in (top sch) u_open /\ a IN sections sch u_open ==>
          on_sec (id_mor sch) u_open a = a)) /\
      (!f g. f IN morphisms /\ g IN morphisms /\ cod f = dom g ==>
        comp f g IN morphisms /\
        dom (comp f g) = dom f /\ cod (comp f g) = cod g /\
        (!x. x IN pts (dom f) ==>
          base (comp f g) x = base g (base f x)) /\
        (!u_open a. open_in (top (cod g)) u_open /\ a IN sections (cod g) u_open ==>
          on_sec (comp f g) u_open a =
          on_sec f (PREIMAGE (base g) u_open INTER pts (dom g))
            (on_sec g u_open a))) /\
      (!f. f IN morphisms ==>
        comp (id_mor (dom f)) f = f /\
        comp f (id_mor (cod f)) = f) /\
      (!f g h.
        f IN morphisms /\ g IN morphisms /\ h IN morphisms /\
        cod f = dom g /\ cod g = dom h ==>
        comp (comp f g) h = comp f (comp g h)) /\
      (!sch u_open. sch IN schemes /\ open_in (top sch) u_open ==>
        open_obj sch u_open IN schemes /\
        pts (open_obj sch u_open) = u_open /\
        top (open_obj sch u_open) = subtopology (top sch) u_open /\
        (!v_open. open_in (top sch) v_open /\ v_open SUBSET u_open ==>
          sections (open_obj sch u_open) v_open = sections sch v_open /\
          zero (open_obj sch u_open) v_open = zero sch v_open /\
          ring_one (open_obj sch u_open) v_open = ring_one sch v_open /\
          add (open_obj sch u_open) v_open = add sch v_open /\
          mul (open_obj sch u_open) v_open = mul sch v_open /\
          neg (open_obj sch u_open) v_open = neg sch v_open /\
          pow (open_obj sch u_open) v_open = pow sch v_open) /\
        (!v_open w_open a.
          open_in (top sch) v_open /\ open_in (top sch) w_open /\
          w_open SUBSET v_open /\ v_open SUBSET u_open /\ a IN sections sch v_open ==>
          res (open_obj sch u_open) v_open w_open a = res sch v_open w_open a) /\
        open_inclusion sch u_open IN morphisms /\
        dom (open_inclusion sch u_open) = open_obj sch u_open /\
        cod (open_inclusion sch u_open) = sch /\
        (!x. x IN u_open ==> base (open_inclusion sch u_open) x = x) /\
        (!v_open a. open_in (top sch) v_open /\ a IN sections sch v_open ==>
          on_sec (open_inclusion sch u_open) v_open a =
          res sch v_open (v_open INTER u_open) a)) /\
      (!f u_open. f IN morphisms /\ open_in (top (cod f)) u_open ==>
        restrict f u_open IN morphisms /\
        dom (restrict f u_open) =
          open_obj (dom f) (PREIMAGE (base f) u_open INTER pts (dom f)) /\
        cod (restrict f u_open) = open_obj (cod f) u_open /\
        (!x. x IN PREIMAGE (base f) u_open INTER pts (dom f) ==>
          base (restrict f u_open) x = base f x) /\
        (!v_open a. open_in (top (cod f)) v_open /\ v_open SUBSET u_open /\
          a IN sections (cod f) v_open ==>
          on_sec (restrict f u_open) v_open a = on_sec f v_open a)) /\
      (!f g. f IN morphisms /\ g IN morphisms /\ cod f = cod g ==>
        pullback_obj f g IN schemes /\
        pullback_fst f g IN morphisms /\
        pullback_snd f g IN morphisms /\
        dom (pullback_fst f g) = pullback_obj f g /\
        cod (pullback_fst f g) = dom f /\
        dom (pullback_snd f g) = pullback_obj f g /\
        cod (pullback_snd f g) = dom g /\
        comp (pullback_fst f g) f = comp (pullback_snd f g) g /\
        (!test_scheme u v.
          test_scheme IN schemes /\ u IN morphisms /\ v IN morphisms /\
          dom u = test_scheme /\ dom v = test_scheme /\
          cod u = dom f /\ cod v = dom g /\
          comp u f = comp v g ==>
          pullback_lift f g u v IN morphisms /\
          dom (pullback_lift f g u v) = test_scheme /\
          cod (pullback_lift f g u v) = pullback_obj f g /\
          comp (pullback_lift f g u v) (pullback_fst f g) = u /\
          comp (pullback_lift f g u v) (pullback_snd f g) = v /\
          (!w. w IN morphisms /\ dom w = test_scheme /\
               cod w = pullback_obj f g /\
               comp w (pullback_fst f g) = u /\
               comp w (pullback_snd f g) = v ==>
               w = pullback_lift f g u v))) /\
      (!f. f IN morphisms ==>
        diagonal f IN morphisms /\
        dom (diagonal f) = dom f /\
        cod (diagonal f) = pullback_obj f f /\
        comp (diagonal f) (pullback_fst f f) = id_mor (dom f) /\
        comp (diagonal f) (pullback_snd f f) = id_mor (dom f))``);

val q8066795_affine_morphism_def = new_definition (
  "q8066795_affine_morphism_def",
  ``q8066795_affine_morphism
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (sections : 's -> 'p set -> 'a set)
      (zero : 's -> 'p set -> 'a) (ring_one : 's -> 'p set -> 'a)
      (add : 's -> 'p set -> 'a -> 'a -> 'a)
      (mul : 's -> 'p set -> 'a -> 'a -> 'a)
      (neg : 's -> 'p set -> 'a -> 'a)
      (pow : 's -> 'p set -> 'a -> num -> 'a)
      (res : 's -> 'p set -> 'p set -> 'a -> 'a)
      (dom : 'm -> 's) (cod : 'm -> 's)
      (base : 'm -> 'p -> 'p) (m : 'm) <=>
      !v_open. q8066795_affine_open
             pts top sections zero ring_one add mul neg pow res (cod m) v_open
          ==>
          q8066795_affine_open
            pts top sections zero ring_one add mul neg pow res (dom m)
            (PREIMAGE (base m) v_open INTER pts (dom m))``);

val q8066795_finite_morphism_def = new_definition (
  "q8066795_finite_morphism_def",
  ``q8066795_finite_morphism
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (sections : 's -> 'p set -> 'a set)
      (zero : 's -> 'p set -> 'a) (ring_one : 's -> 'p set -> 'a)
      (add : 's -> 'p set -> 'a -> 'a -> 'a)
      (mul : 's -> 'p set -> 'a -> 'a -> 'a)
      (neg : 's -> 'p set -> 'a -> 'a)
      (pow : 's -> 'p set -> 'a -> num -> 'a)
      (res : 's -> 'p set -> 'p set -> 'a -> 'a)
      (dom : 'm -> 's) (cod : 'm -> 's)
      (base : 'm -> 'p -> 'p)
      (on_sec : 'm -> 'p set -> 'a -> 'a)
      (m : 'm) <=>
      q8066795_affine_morphism
        pts top sections zero ring_one add mul neg pow res dom cod base m /\
      !v_open. q8066795_affine_open
             pts top sections zero ring_one add mul neg pow res (cod m) v_open
          ==>
          q8066795_module_finite
            (sections (cod m) v_open) (zero (cod m) v_open) (ring_one (cod m) v_open)
            (add (cod m) v_open) (mul (cod m) v_open)
            (neg (cod m) v_open) (pow (cod m) v_open)
            (sections (dom m) (PREIMAGE (base m) v_open INTER pts (dom m)))
            (zero (dom m) (PREIMAGE (base m) v_open INTER pts (dom m)))
            (ring_one (dom m) (PREIMAGE (base m) v_open INTER pts (dom m)))
            (add (dom m) (PREIMAGE (base m) v_open INTER pts (dom m)))
            (mul (dom m) (PREIMAGE (base m) v_open INTER pts (dom m)))
            (neg (dom m) (PREIMAGE (base m) v_open INTER pts (dom m)))
            (pow (dom m) (PREIMAGE (base m) v_open INTER pts (dom m)))
            (on_sec m v_open)``);

val q8066795_locally_finite_type_def = new_definition (
  "q8066795_locally_finite_type_def",
  ``q8066795_locally_finite_type
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (sections : 's -> 'p set -> 'a set)
      (zero : 's -> 'p set -> 'a) (ring_one : 's -> 'p set -> 'a)
      (add : 's -> 'p set -> 'a -> 'a -> 'a)
      (mul : 's -> 'p set -> 'a -> 'a -> 'a)
      (neg : 's -> 'p set -> 'a -> 'a)
      (pow : 's -> 'p set -> 'a -> num -> 'a)
      (res : 's -> 'p set -> 'p set -> 'a -> 'a)
      (dom : 'm -> 's) (cod : 'm -> 's)
      (base : 'm -> 'p -> 'p)
      (on_sec : 'm -> 'p set -> 'a -> 'a)
      (m : 'm) <=>
      !v_open x.
        q8066795_affine_open
          pts top sections zero ring_one add mul neg pow res (cod m) v_open /\
        x IN PREIMAGE (base m) v_open INTER pts (dom m)
        ==>
        ?u_open. x IN u_open /\ u_open SUBSET PREIMAGE (base m) v_open INTER pts (dom m) /\
          q8066795_affine_open
            pts top sections zero ring_one add mul neg pow res (dom m) u_open /\
          q8066795_finite_type
            (sections (cod m) v_open) (zero (cod m) v_open) (ring_one (cod m) v_open)
            (add (cod m) v_open) (mul (cod m) v_open)
            (neg (cod m) v_open) (pow (cod m) v_open)
            (sections (dom m) u_open) (zero (dom m) u_open) (ring_one (dom m) u_open)
            (add (dom m) u_open) (mul (dom m) u_open)
            (neg (dom m) u_open) (pow (dom m) u_open)
            (\a. res (dom m)
              (PREIMAGE (base m) v_open INTER pts (dom m)) u_open
              (on_sec m v_open a))``);

val q8066795_pullback_square_def = new_definition (
  "q8066795_pullback_square_def",
  ``q8066795_pullback_square
      (morphisms : 'm set)
      (dom : 'm -> 's) (cod : 'm -> 's)
      (comp : 'm -> 'm -> 'm)
      (f : 'm) (g : 'm) (to_source : 'm) (to_base : 'm) <=>
      f IN morphisms /\ g IN morphisms /\
      to_source IN morphisms /\ to_base IN morphisms /\
      cod f = cod g /\
      dom to_source = dom to_base /\
      cod to_source = dom f /\ cod to_base = dom g /\
      comp to_source f = comp to_base g /\
      (!u v.
        u IN morphisms /\ v IN morphisms /\
        dom u = dom v /\ cod u = dom f /\ cod v = dom g /\
        comp u f = comp v g
        ==>
        ?!w. w IN morphisms /\
          dom w = dom u /\ cod w = dom to_source /\
          comp w to_source = u /\ comp w to_base = v)``);

val q8066795_universally_closed_def = new_definition (
  "q8066795_universally_closed_def",
  ``q8066795_universally_closed
      (morphisms : 'm set)
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (dom : 'm -> 's) (cod : 'm -> 's)
      (base : 'm -> 'p -> 'p)
      (comp : 'm -> 'm -> 'm)
      (m : 'm) <=>
      !g to_source to_base.
        q8066795_pullback_square
          morphisms dom cod comp m g to_source to_base
        ==>
        q8066795_closed_map pts top dom cod base to_base``);

val q8066795_separated_def = new_definition (
  "q8066795_separated_def",
  ``q8066795_separated
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (sections : 's -> 'p set -> 'a set)
      (res : 's -> 'p set -> 'p set -> 'a -> 'a)
      (dom : 'm -> 's) (cod : 'm -> 's)
      (base : 'm -> 'p -> 'p)
      (on_sec : 'm -> 'p set -> 'a -> 'a)
      (diagonal : 'm -> 'm) (m : 'm) <=>
      q8066795_closed_immersion
        pts top sections res dom cod base on_sec (diagonal m)``);

val q8066795_proper_morphism_def = new_definition (
  "q8066795_proper_morphism_def",
  ``q8066795_proper_morphism
      (morphisms : 'm set)
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (sections : 's -> 'p set -> 'a set)
      (zero : 's -> 'p set -> 'a) (ring_one : 's -> 'p set -> 'a)
      (add : 's -> 'p set -> 'a -> 'a -> 'a)
      (mul : 's -> 'p set -> 'a -> 'a -> 'a)
      (neg : 's -> 'p set -> 'a -> 'a)
      (pow : 's -> 'p set -> 'a -> num -> 'a)
      (res : 's -> 'p set -> 'p set -> 'a -> 'a)
      (dom : 'm -> 's) (cod : 'm -> 's)
      (base : 'm -> 'p -> 'p)
      (on_sec : 'm -> 'p set -> 'a -> 'a)
      (comp : 'm -> 'm -> 'm)
      (diagonal : 'm -> 'm) (m : 'm) <=>
      q8066795_separated pts top sections res dom cod base on_sec diagonal m /\
      q8066795_universally_closed
        morphisms pts top dom cod base comp m /\
      q8066795_locally_finite_type
        pts top sections zero ring_one add mul neg pow res
        dom cod base on_sec m``);

val exists_isFinite_morphismRestrict_of_finite_preimage_singleton =
  ``!(schemes : 's set) (morphisms : 'm set)
      (pts : 's -> 'p set) (top : 's -> 'p topology)
      (sections : 's -> 'p set -> 'a set)
      (zero : 's -> 'p set -> 'a) (ring_one : 's -> 'p set -> 'a)
      (add : 's -> 'p set -> 'a -> 'a -> 'a)
      (mul : 's -> 'p set -> 'a -> 'a -> 'a)
      (neg : 's -> 'p set -> 'a -> 'a)
      (pow : 's -> 'p set -> 'a -> num -> 'a)
      (res : 's -> 'p set -> 'p set -> 'a -> 'a)
      (dom : 'm -> 's) (cod : 'm -> 's)
      (base : 'm -> 'p -> 'p)
      (on_sec : 'm -> 'p set -> 'a -> 'a)
      (id_mor : 's -> 'm) (comp : 'm -> 'm -> 'm)
      (open_obj : 's -> 'p set -> 's)
      (open_inclusion : 's -> 'p set -> 'm)
      (restrict : 'm -> 'p set -> 'm)
      (pullback_obj : 'm -> 'm -> 's)
      (pullback_fst : 'm -> 'm -> 'm)
      (pullback_snd : 'm -> 'm -> 'm)
      (pullback_lift : 'm -> 'm -> 'm -> 'm -> 'm)
      (diagonal : 'm -> 'm)
      (source : 's) (target : 's) (f : 'm) (y : 'p).
      q8066795_geometry
        schemes morphisms pts top sections zero ring_one add mul neg pow res
        dom cod base on_sec id_mor comp open_obj open_inclusion restrict
        pullback_obj pullback_fst pullback_snd pullback_lift diagonal /\
      f IN morphisms /\ dom f = source /\ cod f = target /\
      y IN pts target /\
      q8066795_proper_morphism
        morphisms pts top sections zero ring_one add mul neg pow res
        dom cod base on_sec comp diagonal f /\
      FINITE {x | x IN pts source /\ base f x = y}
      ==>
      ?v_open. open_in (top target) v_open /\ y IN v_open /\
        q8066795_finite_morphism
          pts top sections zero ring_one add mul neg pow res
          dom cod base on_sec (restrict f v_open)``;
