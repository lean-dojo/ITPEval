(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q595466, "Dini's theorem": a monotone family of continuous functions into
  an ordered normed lattice group, indexed by an arbitrary preorder, that
  converges pointwise along atTop converges locally uniformly. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory topologyTheory;

val q595466_preorder_def = new_definition (
  "q595466_preorder_def",
  ``q595466_preorder (carrier : 'i set) (leq : 'i -> 'i -> bool) <=>
      (!i. i IN carrier ==> leq i i) /\
      (!i j k.
        i IN carrier /\ j IN carrier /\ k IN carrier /\
        leq i j /\ leq j k
        ==>
        leq i k)``);

val q595466_directed_def = new_definition (
  "q595466_directed_def",
  ``q595466_directed
      (carrier : 'i set) (leq : 'i -> 'i -> bool) <=>
      carrier <> {} /\
      !i j.
        i IN carrier /\ j IN carrier
        ==>
        ?k. k IN carrier /\ leq i k /\ leq j k``);

val q595466_eventually_at_top_def = new_definition (
  "q595466_eventually_at_top_def",
  ``q595466_eventually_at_top
      (carrier : 'i set) (leq : 'i -> 'i -> bool)
      (p : 'i -> bool) <=>
      ~q595466_directed carrier leq \/
      ?i0.
        i0 IN carrier /\
        !i. i IN carrier /\ leq i0 i ==> p i``);

val q595466_normed_add_comm_group_def = new_definition (
  "q595466_normed_add_comm_group_def",
  ``q595466_normed_add_comm_group
      (zero : 'g) (add : 'g -> 'g -> 'g)
      (neg : 'g -> 'g) (norm : 'g -> real) <=>
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add x zero = x) /\
      (!x. add x (neg x) = zero) /\
      (!x. 0 <= norm x) /\
      (!x. (norm x = 0) <=> (x = zero)) /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y)``);

val q595466_lattice_def = new_definition (
  "q595466_lattice_def",
  ``q595466_lattice
      (leq : 'g -> 'g -> bool)
      (inf : 'g -> 'g -> 'g) (sup : 'g -> 'g -> 'g) <=>
      (!x. leq x x) /\
      (!x y. leq x y /\ leq y x ==> x = y) /\
      (!x y z. leq x y /\ leq y z ==> leq x z) /\
      (!x y. leq (inf x y) x /\ leq (inf x y) y) /\
      (!x y z. leq z x /\ leq z y ==> leq z (inf x y)) /\
      (!x y. leq x (sup x y) /\ leq y (sup x y)) /\
      (!x y z. leq x z /\ leq y z ==> leq (sup x y) z)``);

val q595466_ordered_add_monoid_def = new_definition (
  "q595466_ordered_add_monoid_def",
  ``q595466_ordered_add_monoid
      (leq : 'g -> 'g -> bool) (add : 'g -> 'g -> 'g) <=>
      (!a b c. leq a b ==> leq (add a c) (add b c)) /\
      (!a b c. leq a b ==> leq (add c a) (add c b))``);

val q595466_solid_norm_def = new_definition (
  "q595466_solid_norm_def",
  ``q595466_solid_norm
      (leq : 'g -> 'g -> bool) (sup : 'g -> 'g -> 'g)
      (neg : 'g -> 'g) (norm : 'g -> real) <=>
      !x y.
        leq (sup x (neg x)) (sup y (neg y))
        ==>
        norm x <= norm y``);

val q595466_continuous_def = new_definition (
  "q595466_continuous_def",
  ``q595466_continuous
      (top : 'a topology)
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (norm : 'g -> real) (h : 'a -> 'g) <=>
      !x epsilon.
        x IN topspace top /\ 0 < epsilon ==>
        ?u : 'a set.
          open_in top u /\
          x IN u /\
          !y. y IN u ==>
              norm (add (h y) (neg (h x))) < epsilon``);

val q595466_tendsto_at_top_def = new_definition (
  "q595466_tendsto_at_top_def",
  ``q595466_tendsto_at_top
      (index_carrier : 'i set) (leI : 'i -> 'i -> bool)
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (norm : 'g -> real) (u : 'i -> 'g) (ell : 'g) <=>
      !epsilon.
        0 < epsilon ==>
        q595466_eventually_at_top index_carrier leI
          (\i. norm (add (u i) (neg ell)) < epsilon)``);

val q595466_tendsto_locally_uniformly_def = new_definition (
  "q595466_tendsto_locally_uniformly_def",
  ``q595466_tendsto_locally_uniformly
      (top : 'a topology)
      (index_carrier : 'i set) (leI : 'i -> 'i -> bool)
      (add : 'g -> 'g -> 'g) (neg : 'g -> 'g)
      (norm : 'g -> real)
      (F : 'i -> 'a -> 'g) (f : 'a -> 'g) <=>
      !epsilon x.
        x IN topspace top /\ 0 < epsilon ==>
        ?u : 'a set.
          open_in top u /\
          x IN u /\
          q595466_eventually_at_top index_carrier leI
            (\i. !y. y IN u ==>
                norm (add (F i y) (neg (f y))) < epsilon)``);

val Monotone_tendstoLocallyUniformly_of_forall_tendsto =
  ``!(top : 'a topology)
      (index_carrier : 'i set) (leI : 'i -> 'i -> bool)
      (zero : 'g) (add : 'g -> 'g -> 'g)
      (neg : 'g -> 'g) (norm : 'g -> real)
      (leG : 'g -> 'g -> bool)
      (inf : 'g -> 'g -> 'g) (sup : 'g -> 'g -> 'g)
      (F : 'i -> 'a -> 'g) (f : 'a -> 'g).
      q595466_preorder index_carrier leI /\
      q595466_normed_add_comm_group zero add neg norm /\
      q595466_lattice leG inf sup /\
      q595466_solid_norm leG sup neg norm /\
      q595466_ordered_add_monoid leG add /\
      (!i.
        i IN index_carrier ==>
        q595466_continuous top add neg norm (F i)) /\
      (!i j.
        i IN index_carrier /\ j IN index_carrier /\ leI i j
        ==>
        !x. x IN topspace top ==> leG (F i x) (F j x)) /\
      q595466_continuous top add neg norm f /\
      (!x. x IN topspace top ==>
        q595466_tendsto_at_top index_carrier leI add neg norm
          (\i. F i x) (f x))
      ==>
      q595466_tendsto_locally_uniformly
        top index_carrier leI add neg norm F f``;
