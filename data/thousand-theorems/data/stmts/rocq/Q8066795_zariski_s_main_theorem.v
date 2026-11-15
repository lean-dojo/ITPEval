(**
  Statement-only formalization of corpus artifact Q8066795
  (thousand-theorems__rocq__Q8066795), catalogued as "Zariski's main
  theorem": a proper morphism of schemes whose fiber over a point is finite
  is finite after restriction to some open neighborhood of that point.
  This file contains no proof.
*)

From Stdlib Require Import List.
Import ListNotations.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.

Definition q_set (A : Type) := A -> Prop.

Definition q_subset {A : Type} (U V : q_set A) : Prop :=
  forall x, U x -> V x.

Definition q_same_set {A : Type} (U V : q_set A) : Prop :=
  forall x, U x <-> V x.

Definition q_same_set_refl {A : Type} (U : q_set A) :
    q_same_set U U :=
  fun _ => conj (fun h => h) (fun h => h).

Definition q_same_set_symm {A : Type} {U V : q_set A}
    (h : q_same_set U V) : q_same_set V U :=
  fun x => conj (proj2 (h x)) (proj1 (h x)).

Definition q_same_set_trans {A : Type} {U V W : q_set A}
    (hUV : q_same_set U V) (hVW : q_same_set V W) :
    q_same_set U W :=
  fun x => conj
    (fun hx => proj1 (hVW x) (proj1 (hUV x) hx))
    (fun hx => proj2 (hUV x) (proj2 (hVW x) hx)).

Definition q_empty {A : Type} : q_set A := fun _ => False.
Definition q_full {A : Type} : q_set A := fun _ => True.

Definition q_inter {A : Type} (U V : q_set A) : q_set A :=
  fun x => U x /\ V x.

Definition q_compl {A : Type} (U : q_set A) : q_set A :=
  fun x => ~ U x.

Definition q_union {A I : Type} (U : I -> q_set A) : q_set A :=
  fun x => exists i, U i x.

Definition q_preimage {A B : Type} (f : A -> B) (V : q_set B) : q_set A :=
  fun x => V (f x).

Definition q_image {A B : Type} (f : A -> B) (U : q_set A) : q_set B :=
  fun y => exists x, U x /\ f x = y.

Definition q_finite_set {A : Type} (U : q_set A) : Prop :=
  exists l : list A, forall x, U x <-> In x l.

Definition q_subset_refl {A : Type} (U : q_set A) : q_subset U U :=
  fun _ h => h.

Definition q_inter_left {A : Type} (U V : q_set A) :
    q_subset (q_inter U V) U :=
  fun _ h => proj1 h.

Definition q_inter_right {A : Type} (U V : q_set A) :
    q_subset (q_inter U V) V :=
  fun _ h => proj2 h.

Record q_comm_ring (A : Type) := {
  q_zero : A;
  q_one : A;
  q_add : A -> A -> A;
  q_mul : A -> A -> A;
  q_neg : A -> A;
  q_add_assoc : forall a b c,
    q_add a (q_add b c) = q_add (q_add a b) c;
  q_add_comm : forall a b, q_add a b = q_add b a;
  q_add_zero : forall a, q_add a q_zero = a;
  q_add_neg : forall a, q_add a (q_neg a) = q_zero;
  q_mul_assoc : forall a b c,
    q_mul a (q_mul b c) = q_mul (q_mul a b) c;
  q_mul_comm : forall a b, q_mul a b = q_mul b a;
  q_mul_one : forall a, q_mul a q_one = a;
  q_left_distrib : forall a b c,
    q_mul a (q_add b c) = q_add (q_mul a b) (q_mul a c)
}.

Arguments q_zero {A} _.
Arguments q_one {A} _.
Arguments q_add {A} _ _ _.
Arguments q_mul {A} _ _ _.
Arguments q_neg {A} _ _.

Definition q_is_ring_hom {A B : Type}
    (RA : q_comm_ring A) (RB : q_comm_ring B) (f : A -> B) : Prop :=
  f (q_zero RA) = q_zero RB /\
  f (q_one RA) = q_one RB /\
  (forall a b, f (q_add RA a b) = q_add RB (f a) (f b)) /\
  (forall a b, f (q_mul RA a b) = q_mul RB (f a) (f b)).

Record q_ideal {A : Type} (R : q_comm_ring A) := {
  q_ideal_contains : A -> Prop;
  q_ideal_zero : q_ideal_contains (q_zero R);
  q_ideal_add : forall a b,
    q_ideal_contains a ->
    q_ideal_contains b ->
    q_ideal_contains (q_add R a b);
  q_ideal_neg : forall a,
    q_ideal_contains a ->
    q_ideal_contains (q_neg R a);
  q_ideal_mul : forall a b,
    q_ideal_contains a ->
    q_ideal_contains (q_mul R a b)
}.

Arguments q_ideal_contains {A R} _ _.

Definition q_same_ideal {A : Type} {R : q_comm_ring A}
    (I J : q_ideal R) : Prop :=
  forall a, q_ideal_contains I a <-> q_ideal_contains J a.

Definition q_is_prime_ideal {A : Type} {R : q_comm_ring A}
    (I : q_ideal R) : Prop :=
  ~ q_ideal_contains I (q_one R) /\
  forall a b,
    q_ideal_contains I (q_mul R a b) ->
    q_ideal_contains I a \/ q_ideal_contains I b.

Definition q_is_unit {A : Type} (R : q_comm_ring A) (a : A) : Prop :=
  exists b, q_mul R a b = q_one R /\ q_mul R b a = q_one R.

Definition q_is_localization_at {A B : Type}
    (RA : q_comm_ring A) (RB : q_comm_ring B)
    (phi : A -> B) (r : A) : Prop :=
  q_is_ring_hom RA RB phi /\
  q_is_unit RB (phi r) /\
  forall (C : Type) (RC : q_comm_ring C) (psi : A -> C),
    q_is_ring_hom RA RC psi ->
    q_is_unit RC (psi r) ->
    exists theta : B -> C,
      q_is_ring_hom RB RC theta /\
      (forall a, theta (phi a) = psi a) /\
      forall theta' : B -> C,
        q_is_ring_hom RB RC theta' ->
        (forall a, theta' (phi a) = psi a) ->
        forall b, theta' b = theta b.

Fixpoint q_linear_combination {A B : Type}
    (RA : q_comm_ring A) (RB : q_comm_ring B) (phi : A -> B)
    (coefficients : list A) (generators : list B) : B :=
  match coefficients, generators with
  | a :: coefficients', b :: generators' =>
      q_add RB (q_mul RB (phi a) b)
        (q_linear_combination RA RB phi coefficients' generators')
  | _, _ => q_zero RB
  end.

Definition q_is_module_finite_algebra {A B : Type}
    (RA : q_comm_ring A) (RB : q_comm_ring B) (phi : A -> B) : Prop :=
  q_is_ring_hom RA RB phi /\
  exists generators : list B,
    forall b : B,
      exists coefficients : list A,
        length coefficients = length generators /\
        q_linear_combination RA RB phi coefficients generators = b.

Inductive q_generated_subalgebra {A B : Type}
    (RA : q_comm_ring A) (RB : q_comm_ring B) (phi : A -> B)
    (generators : list B) : B -> Prop :=
| q_generated_scalar : forall a,
    q_generated_subalgebra RA RB phi generators (phi a)
| q_generated_generator : forall b,
    In b generators ->
    q_generated_subalgebra RA RB phi generators b
| q_generated_zero :
    q_generated_subalgebra RA RB phi generators (q_zero RB)
| q_generated_one :
    q_generated_subalgebra RA RB phi generators (q_one RB)
| q_generated_add : forall b c,
    q_generated_subalgebra RA RB phi generators b ->
    q_generated_subalgebra RA RB phi generators c ->
    q_generated_subalgebra RA RB phi generators (q_add RB b c)
| q_generated_mul : forall b c,
    q_generated_subalgebra RA RB phi generators b ->
    q_generated_subalgebra RA RB phi generators c ->
    q_generated_subalgebra RA RB phi generators (q_mul RB b c)
| q_generated_neg : forall b,
    q_generated_subalgebra RA RB phi generators b ->
    q_generated_subalgebra RA RB phi generators (q_neg RB b).

Definition q_is_finite_type_algebra {A B : Type}
    (RA : q_comm_ring A) (RB : q_comm_ring B) (phi : A -> B) : Prop :=
  q_is_ring_hom RA RB phi /\
  exists generators : list B,
    forall b, q_generated_subalgebra RA RB phi generators b.

Record q_topological_space (P : Type) := {
  q_is_open : q_set P -> Prop;
  q_open_ext : forall U V,
    q_same_set U V -> q_is_open U -> q_is_open V;
  q_open_empty : q_is_open q_empty;
  q_open_full : q_is_open q_full;
  q_open_inter : forall U V,
    q_is_open U -> q_is_open V -> q_is_open (q_inter U V);
  q_open_union : forall (I : Type) (U : I -> q_set P),
    (forall i, q_is_open (U i)) ->
    q_is_open (q_union U)
}.

Arguments q_is_open {P} _ _.

Definition q_is_closed {P : Type} (T : q_topological_space P)
    (Z : q_set P) : Prop :=
  q_is_open T (q_compl Z).

Record q_open {P : Type} (T : q_topological_space P) := {
  q_open_carrier : q_set P;
  q_open_witness : q_is_open T q_open_carrier
}.

Arguments q_open_carrier {P T} _ _.
Arguments q_open_witness {P T} _.

Definition q_open_of_set {P : Type} (T : q_topological_space P)
    (U : q_set P) (hU : q_is_open T U) : q_open T :=
  {| q_open_carrier := U; q_open_witness := hU |}.

Definition q_open_subset {P : Type} {T : q_topological_space P}
    (U V : q_open T) : Prop :=
  q_subset (q_open_carrier U) (q_open_carrier V).

Definition q_open_meet {P : Type} {T : q_topological_space P}
    (U V : q_open T) : q_open T :=
  @q_open_of_set P T
    (q_inter (q_open_carrier U) (q_open_carrier V))
    (@q_open_inter P T _ _
      (q_open_witness U) (q_open_witness V)).

Record q_ringed_space := {
  q_points : Type;
  q_topology : q_topological_space q_points;
  q_sections : q_open q_topology -> Type;
  q_section_ring : forall U, q_comm_ring (q_sections U);
  q_reindex : forall U V,
    q_same_set (q_open_carrier U) (q_open_carrier V) ->
    q_sections U -> q_sections V;
  q_reindex_ring_hom : forall U V
      (h : q_same_set (q_open_carrier U) (q_open_carrier V)),
    q_is_ring_hom (q_section_ring U) (q_section_ring V)
      (@q_reindex U V h);
  q_reindex_proof_irrelevant : forall U V
      (h h' : q_same_set (q_open_carrier U) (q_open_carrier V))
      (s : q_sections U),
    @q_reindex U V h s = @q_reindex U V h' s;
  q_reindex_identity : forall U (s : q_sections U),
    @q_reindex U U
      (@q_same_set_refl q_points (q_open_carrier U)) s = s;
  q_reindex_inverse : forall U V
      (h : q_same_set (q_open_carrier U) (q_open_carrier V))
      (s : q_sections U),
    @q_reindex V U (q_same_set_symm h)
      (@q_reindex U V h s) = s;
  q_reindex_composition : forall U V W
      (hUV : q_same_set (q_open_carrier U) (q_open_carrier V))
      (hVW : q_same_set (q_open_carrier V) (q_open_carrier W))
      (s : q_sections U),
    @q_reindex V W hVW (@q_reindex U V hUV s) =
    @q_reindex U W (q_same_set_trans hUV hVW) s;
  q_restrict : forall U V,
    q_open_subset U V -> q_sections V -> q_sections U;
  q_restrict_ring_hom : forall U V (h : q_open_subset U V),
    q_is_ring_hom (q_section_ring V) (q_section_ring U)
      (@q_restrict U V h);
  q_restrict_proof_irrelevant : forall U V
      (h h' : q_open_subset U V) (s : q_sections V),
    @q_restrict U V h s = @q_restrict U V h' s;
  q_restrict_identity : forall U (s : q_sections U),
    @q_restrict U U
      (@q_subset_refl q_points (q_open_carrier U)) s = s;
  q_restrict_same_set : forall U V
      (hEq : q_same_set (q_open_carrier U) (q_open_carrier V))
      (hSub : q_open_subset U V) (s : q_sections V),
    @q_restrict U V hSub s =
    @q_reindex V U (q_same_set_symm hEq) s;
  q_restrict_composition : forall U V W
      (hUV : q_open_subset U V) (hVW : q_open_subset V W)
      (s : q_sections W),
    @q_restrict U V hUV (@q_restrict V W hVW s) =
    @q_restrict U W (fun x hx => hVW x (hUV x hx)) s;
  q_reindex_restrict : forall U U' V V'
      (hUU' : q_same_set (q_open_carrier U) (q_open_carrier U'))
      (hVV' : q_same_set (q_open_carrier V) (q_open_carrier V'))
      (hUV : q_open_subset U V) (hU'V' : q_open_subset U' V')
      (s : q_sections V),
    @q_reindex U U' hUU' (@q_restrict U V hUV s) =
    @q_restrict U' V' hU'V' (@q_reindex V V' hVV' s);
  q_sheaf_gluing : forall (I : Type) (U : q_open q_topology)
      (O : I -> q_open q_topology)
      (hOU : forall i, q_open_subset (O i) U)
      (hcover : forall x, q_open_carrier U x ->
        exists i, q_open_carrier (O i) x)
      (local : forall i, q_sections (O i)),
    (forall i j,
      @q_restrict (q_open_meet (O i) (O j)) (O i)
        (@q_inter_left q_points
          (q_open_carrier (O i)) (q_open_carrier (O j)))
        (local i) =
      @q_restrict (q_open_meet (O i) (O j)) (O j)
        (@q_inter_right q_points
          (q_open_carrier (O i)) (q_open_carrier (O j)))
        (local j)) ->
    exists global : q_sections U,
      (forall i, @q_restrict (O i) U (hOU i) global = local i) /\
      forall global' : q_sections U,
        (forall i, @q_restrict (O i) U (hOU i) global' = local i) ->
        global' = global
}.

Arguments q_points _ : clear implicits.
Arguments q_topology _ : clear implicits.
Arguments q_sections _ _ : clear implicits.
Arguments q_section_ring _ _ : clear implicits.
Arguments q_reindex _ _ _ _ _ : clear implicits.
Arguments q_restrict _ _ _ _ _ : clear implicits.

Definition q_unit_germ (R : q_ringed_space)
    (U : q_open (q_topology R)) (x : q_points R)
    (s : q_sections R U) : Prop :=
  exists (V : q_open (q_topology R)) (hVU : q_open_subset V U),
    q_open_carrier V x /\
    exists t : q_sections R V,
      q_mul (q_section_ring R V) (q_restrict R V U hVU s) t =
        q_one (q_section_ring R V) /\
      q_mul (q_section_ring R V) t (q_restrict R V U hVU s) =
        q_one (q_section_ring R V).

Arguments q_unit_germ _ _ _ _ : clear implicits.

Definition q_is_affine_open (R : q_ringed_space)
    (U : q_open (q_topology R)) : Prop :=
  exists point_prime :
      q_points R -> q_ideal (q_section_ring R U),
    (forall x, q_open_carrier U x ->
      q_is_prime_ideal (point_prime x)) /\
    (forall x (hx : q_open_carrier U x) (s : q_sections R U),
      q_ideal_contains (point_prime x) s <->
      ~ q_unit_germ R U x s) /\
    (forall x x',
      q_open_carrier U x -> q_open_carrier U x' ->
      q_same_ideal (point_prime x) (point_prime x') ->
      x = x') /\
    (forall p : q_ideal (q_section_ring R U),
      q_is_prime_ideal p ->
      exists x, q_open_carrier U x /\
        q_same_ideal (point_prime x) p) /\
    (forall W : q_open (q_topology R),
      q_open_subset W U ->
      forall x, q_open_carrier W x ->
        exists r : q_sections R U,
          let D := fun z =>
            q_open_carrier U z /\
            ~ q_ideal_contains (point_prime z) r in
          D x /\ q_subset D (q_open_carrier W)) /\
    forall r : q_sections R U,
      let D := fun x =>
        q_open_carrier U x /\
        ~ q_ideal_contains (point_prime x) r in
      exists hD : q_is_open (q_topology R) D,
        q_is_localization_at
          (q_section_ring R U)
          (q_section_ring R
            (@q_open_of_set (q_points R) (q_topology R) D hD))
          (q_restrict R
            (@q_open_of_set (q_points R) (q_topology R) D hD) U
            (fun x hx => proj1 hx))
          r.

Arguments q_is_affine_open _ _ : clear implicits.

Record q_scheme := {
  q_underlying_space : q_ringed_space;
  q_locally_affine : forall x : q_points q_underlying_space,
    exists U : q_open (q_topology q_underlying_space),
      q_open_carrier U x /\
      q_is_affine_open q_underlying_space U
}.

Definition q_scheme_points (X : q_scheme) : Type :=
  q_points (q_underlying_space X).

Definition q_scheme_open (X : q_scheme) : Type :=
  q_open (q_topology (q_underlying_space X)).

Definition q_scheme_sections (X : q_scheme)
    (U : q_scheme_open X) : Type :=
  q_sections (q_underlying_space X) U.

Arguments q_scheme_points _ : clear implicits.
Arguments q_scheme_open _ : clear implicits.
Arguments q_scheme_sections _ _ : clear implicits.

Record q_scheme_map (X Y : q_scheme) := {
  q_point_map : q_scheme_points X -> q_scheme_points Y;
  q_preimage_open : forall V : q_scheme_open Y,
    q_is_open (q_topology (q_underlying_space X))
      (q_preimage q_point_map (q_open_carrier V));
  q_pull_section : forall V : q_scheme_open Y,
    q_scheme_sections Y V ->
    q_scheme_sections X
      (@q_open_of_set (q_scheme_points X)
        (q_topology (q_underlying_space X))
        (q_preimage q_point_map (q_open_carrier V))
        (q_preimage_open V))
}.

Arguments q_point_map {X Y} _ _.
Arguments q_preimage_open {X Y} _ _.
Arguments q_pull_section {X Y} _ _ _.

Definition q_map_preimage_open {X Y : q_scheme}
    (f : q_scheme_map X Y) (V : q_scheme_open Y) :
    q_scheme_open X :=
  @q_open_of_set (q_scheme_points X)
    (q_topology (q_underlying_space X))
    (q_preimage (q_point_map f) (q_open_carrier V))
    (q_preimage_open f V).

Definition q_preimage_open_same_set {X Y : q_scheme}
    (f : q_scheme_map X Y) (U V : q_scheme_open Y)
    (h : q_same_set (q_open_carrier U) (q_open_carrier V)) :
    q_same_set
      (q_open_carrier (q_map_preimage_open f U))
      (q_open_carrier (q_map_preimage_open f V)) :=
  fun x => h (q_point_map f x).

Definition q_is_scheme_morphism {X Y : q_scheme}
    (f : q_scheme_map X Y) : Prop :=
  (forall V : q_scheme_open Y,
    q_is_ring_hom
      (q_section_ring (q_underlying_space Y) V)
      (q_section_ring (q_underlying_space X)
        (q_map_preimage_open f V))
      (q_pull_section f V)) /\
  (forall (U V : q_scheme_open Y) (hUV : q_open_subset U V)
      (s : q_scheme_sections Y V),
    q_restrict (q_underlying_space X)
      (q_map_preimage_open f U) (q_map_preimage_open f V)
      (fun x hx => hUV (q_point_map f x) hx)
      (q_pull_section f V s) =
    q_pull_section f U
      (q_restrict (q_underlying_space Y) U V hUV s)) /\
  (forall (U V : q_scheme_open Y)
      (h : q_same_set (q_open_carrier U) (q_open_carrier V))
      (s : q_scheme_sections Y U),
    q_reindex (q_underlying_space X)
      (q_map_preimage_open f U) (q_map_preimage_open f V)
      (@q_preimage_open_same_set X Y f U V h)
      (q_pull_section f U s) =
    q_pull_section f V
      (q_reindex (q_underlying_space Y) U V h s)) /\
  forall (V : q_scheme_open Y)
      (y : q_scheme_points Y) (s : q_scheme_sections Y V)
      (x : q_scheme_points X),
    q_point_map f x = y ->
    q_open_carrier V y ->
    q_unit_germ (q_underlying_space X)
      (q_map_preimage_open f V) x
      (q_pull_section f V s) ->
    q_unit_germ (q_underlying_space Y) V y s.

Definition q_identity_map (X : q_scheme) : q_scheme_map X X :=
  {| q_point_map := fun x => x;
     q_preimage_open := fun V => q_open_witness V;
     q_pull_section := fun V s =>
       q_reindex (q_underlying_space X) V
         (@q_open_of_set (q_scheme_points X)
           (q_topology (q_underlying_space X))
           (q_preimage (fun x => x) (q_open_carrier V))
           (q_open_witness V))
         (fun x => conj (fun hx => hx) (fun hx => hx)) s |}.

Definition q_compose_map {X Y Z : q_scheme}
    (f : q_scheme_map X Y) (g : q_scheme_map Y Z) :
    q_scheme_map X Z :=
  {| q_point_map := fun x => q_point_map g (q_point_map f x);
     q_preimage_open := fun V =>
       q_preimage_open f (q_map_preimage_open g V);
     q_pull_section := fun V s =>
       q_pull_section f (q_map_preimage_open g V)
         (q_pull_section g V s) |}.

Definition q_preimage_same_set {X Y : q_scheme}
    (f g : q_scheme_map X Y)
    (hpoints : forall x, q_point_map f x = q_point_map g x)
    (V : q_scheme_open Y) :
    q_same_set
      (q_open_carrier (q_map_preimage_open f V))
      (q_open_carrier (q_map_preimage_open g V)) :=
  fun x => conj
    (fun hx =>
      eq_ind (q_point_map f x)
        (fun y => q_open_carrier V y) hx
        (q_point_map g x) (hpoints x))
    (fun hx =>
      eq_ind (q_point_map g x)
        (fun y => q_open_carrier V y) hx
        (q_point_map f x) (eq_sym (hpoints x))).

Definition q_maps_agree {X Y : q_scheme}
    (f g : q_scheme_map X Y) : Prop :=
  exists hpoints : forall x, q_point_map f x = q_point_map g x,
    forall (V : q_scheme_open Y) (s : q_scheme_sections Y V),
      q_reindex (q_underlying_space X)
        (q_map_preimage_open f V) (q_map_preimage_open g V)
        (@q_preimage_same_set X Y f g hpoints V)
        (q_pull_section f V s) =
      q_pull_section g V s.

Record q_fiber_product {X Y Z : q_scheme}
    (f : q_scheme_map X Y) (g : q_scheme_map Z Y) := {
  q_pullback_scheme : q_scheme;
  q_pullback_fst : q_scheme_map q_pullback_scheme X;
  q_pullback_snd : q_scheme_map q_pullback_scheme Z;
  q_pullback_fst_morphism : q_is_scheme_morphism q_pullback_fst;
  q_pullback_snd_morphism : q_is_scheme_morphism q_pullback_snd;
  q_pullback_square :
    q_maps_agree
      (q_compose_map q_pullback_fst f)
      (q_compose_map q_pullback_snd g);
  q_pullback_universal : forall
      (W : q_scheme) (a : q_scheme_map W X) (b : q_scheme_map W Z),
    q_is_scheme_morphism a ->
    q_is_scheme_morphism b ->
    q_maps_agree (q_compose_map a f) (q_compose_map b g) ->
    exists u : q_scheme_map W q_pullback_scheme,
      q_is_scheme_morphism u /\
      q_maps_agree (q_compose_map u q_pullback_fst) a /\
      q_maps_agree (q_compose_map u q_pullback_snd) b /\
      forall u' : q_scheme_map W q_pullback_scheme,
        q_is_scheme_morphism u' ->
        q_maps_agree (q_compose_map u' q_pullback_fst) a ->
        q_maps_agree (q_compose_map u' q_pullback_snd) b ->
        q_maps_agree u' u
}.

Arguments q_pullback_scheme {X Y Z f g} _.
Arguments q_pullback_fst {X Y Z f g} _.
Arguments q_pullback_snd {X Y Z f g} _.

Definition q_is_closed_map {X Y : q_scheme}
    (f : q_scheme_map X Y) : Prop :=
  forall Z : q_set (q_scheme_points X),
    q_is_closed (q_topology (q_underlying_space X)) Z ->
    q_is_closed (q_topology (q_underlying_space Y))
      (q_image (q_point_map f) Z).

Definition q_is_ring_isomorphism {A B : Type}
    (RA : q_comm_ring A) (RB : q_comm_ring B) (f : A -> B) : Prop :=
  q_is_ring_hom RA RB f /\
  exists g : B -> A,
    q_is_ring_hom RB RA g /\
    (forall a, g (f a) = a) /\
    forall b, f (g b) = b.

Definition q_is_closed_immersion {X Y : q_scheme}
    (f : q_scheme_map X Y) : Prop :=
  q_is_scheme_morphism f /\
  (forall x x', q_point_map f x = q_point_map f x' -> x = x') /\
  q_is_closed (q_topology (q_underlying_space Y))
    (q_image (q_point_map f) q_full) /\
  (forall U : q_scheme_open X,
    exists V : q_scheme_open Y,
      q_same_set (q_open_carrier U)
        (q_preimage (q_point_map f) (q_open_carrier V))) /\
  forall (V : q_scheme_open Y)
      (x : q_scheme_points X)
      (s : q_scheme_sections X (q_map_preimage_open f V)),
    q_open_carrier V (q_point_map f x) ->
    exists (W : q_scheme_open Y) (hWV : q_open_subset W V),
      q_open_carrier W (q_point_map f x) /\
      exists t : q_scheme_sections Y W,
        q_pull_section f W t =
        q_restrict (q_underlying_space X)
          (q_map_preimage_open f W) (q_map_preimage_open f V)
          (fun z hz => hWV (q_point_map f z) hz) s.

Definition q_is_quasi_compact_subset (X : q_scheme)
    (K : q_set (q_scheme_points X)) : Prop :=
  forall (I : Type) (O : I -> q_scheme_open X),
    (forall x, K x -> exists i, q_open_carrier (O i) x) ->
    exists finite_indices : list I,
      forall x, K x ->
      exists i, In i finite_indices /\ q_open_carrier (O i) x.

Arguments q_is_quasi_compact_subset _ _ : clear implicits.

Definition q_is_quasi_compact_morphism {X Y : q_scheme}
    (f : q_scheme_map X Y) : Prop :=
  forall K : q_set (q_scheme_points Y),
    q_is_quasi_compact_subset Y K ->
    q_is_quasi_compact_subset X (q_preimage (q_point_map f) K).

Definition q_induced_section_map {X Y : q_scheme}
    (f : q_scheme_map X Y)
    (U : q_scheme_open X) (V : q_scheme_open Y)
    (hU : q_open_subset U (q_map_preimage_open f V))
    (s : q_scheme_sections Y V) : q_scheme_sections X U :=
  q_restrict (q_underlying_space X) U
    (q_map_preimage_open f V) hU
    (q_pull_section f V s).

Definition q_is_locally_finite_type {X Y : q_scheme}
    (f : q_scheme_map X Y) : Prop :=
  q_is_scheme_morphism f /\
  forall V : q_scheme_open Y,
    q_is_affine_open (q_underlying_space Y) V ->
    forall x : q_scheme_points X,
      q_open_carrier V (q_point_map f x) ->
      exists (U : q_scheme_open X)
          (hU : q_open_subset U (q_map_preimage_open f V)),
        q_open_carrier U x /\
        q_is_affine_open (q_underlying_space X) U /\
        q_is_finite_type_algebra
          (q_section_ring (q_underlying_space Y) V)
          (q_section_ring (q_underlying_space X) U)
          (@q_induced_section_map X Y f U V hU).

Definition q_is_finite_type_morphism {X Y : q_scheme}
    (f : q_scheme_map X Y) : Prop :=
  q_is_locally_finite_type f /\ q_is_quasi_compact_morphism f.

Definition q_is_finite_morphism {X Y : q_scheme}
    (f : q_scheme_map X Y) : Prop :=
  q_is_scheme_morphism f /\
  forall V : q_scheme_open Y,
    q_is_affine_open (q_underlying_space Y) V ->
    q_is_affine_open (q_underlying_space X)
      (q_map_preimage_open f V) /\
    q_is_module_finite_algebra
      (q_section_ring (q_underlying_space Y) V)
      (q_section_ring (q_underlying_space X)
        (q_map_preimage_open f V))
      (q_pull_section f V).

Definition q_is_finite_over_open {X Y : q_scheme}
    (f : q_scheme_map X Y) (V : q_scheme_open Y) : Prop :=
  q_is_scheme_morphism f /\
  forall W : q_scheme_open Y,
    q_open_subset W V ->
    q_is_affine_open (q_underlying_space Y) W ->
    q_is_affine_open (q_underlying_space X)
      (q_map_preimage_open f W) /\
    q_is_module_finite_algebra
      (q_section_ring (q_underlying_space Y) W)
      (q_section_ring (q_underlying_space X)
        (q_map_preimage_open f W))
      (q_pull_section f W).

Definition q_is_separated {X Y : q_scheme}
    (f : q_scheme_map X Y) : Prop :=
  q_is_scheme_morphism f /\
  forall PB : q_fiber_product f f,
    forall d : q_scheme_map X (q_pullback_scheme PB),
      q_is_scheme_morphism d ->
      q_maps_agree
        (q_compose_map d (q_pullback_fst PB))
        (q_identity_map X) ->
      q_maps_agree
        (q_compose_map d (q_pullback_snd PB))
        (q_identity_map X) ->
      q_is_closed_immersion d.

Definition q_is_universally_closed {X Y : q_scheme}
    (f : q_scheme_map X Y) : Prop :=
  q_is_scheme_morphism f /\
  forall (Z : q_scheme) (g : q_scheme_map Z Y),
    q_is_scheme_morphism g ->
    forall PB : q_fiber_product f g,
      q_is_closed_map (q_pullback_snd PB).

Definition q_is_proper {X Y : q_scheme}
    (f : q_scheme_map X Y) : Prop :=
  q_is_separated f /\
  q_is_universally_closed f /\
  q_is_locally_finite_type f.

Theorem Q8066795_zariski_s_main_theorem :
  forall (X Y : q_scheme) (f : q_scheme_map X Y)
    (y : q_scheme_points Y),
    q_is_proper f ->
    q_finite_set (fun x : q_scheme_points X => q_point_map f x = y) ->
    exists V : q_scheme_open Y,
      q_open_carrier V y /\
      q_is_finite_over_open f V.
Admitted.
