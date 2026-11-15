(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1148215
  (thousand-theorems__rocq__Q1148215), "Mitchell's embedding theorem": every
  abelian category admits a full and faithful functor to modules over a ring
  that preserves finite limits and finite colimits. This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.

Record q1148215_category : Type := {
  q1148215_obj : Type;
  q1148215_hom : q1148215_obj -> q1148215_obj -> Type;
  q1148215_id :
    forall X : q1148215_obj, q1148215_hom X X;
  q1148215_comp :
    forall X Y Z : q1148215_obj,
      q1148215_hom X Y ->
      q1148215_hom Y Z ->
      q1148215_hom X Z;
  q1148215_comp_id_left :
    forall (X Y : q1148215_obj) (f : q1148215_hom X Y),
      @q1148215_comp X X Y (q1148215_id X) f = f;
  q1148215_comp_id_right :
    forall (X Y : q1148215_obj) (f : q1148215_hom X Y),
      @q1148215_comp X Y Y f (q1148215_id Y) = f;
  q1148215_comp_assoc :
    forall (W X Y Z : q1148215_obj)
           (f : q1148215_hom W X)
           (g : q1148215_hom X Y)
           (h : q1148215_hom Y Z),
      @q1148215_comp W Y Z (@q1148215_comp W X Y f g) h =
      @q1148215_comp W X Z f (@q1148215_comp X Y Z g h)
}.

Arguments q1148215_obj _ : clear implicits.
Arguments q1148215_hom _ _ _ : clear implicits.
Arguments q1148215_id {q} _.
Arguments q1148215_comp {q} {X Y Z} _ _.

Record q1148215_abelian_group (A : Type) : Type := {
  q1148215_ag_zero : A;
  q1148215_ag_add : A -> A -> A;
  q1148215_ag_neg : A -> A;
  q1148215_ag_add_assoc :
    forall x y z : A,
      q1148215_ag_add x (q1148215_ag_add y z) =
      q1148215_ag_add (q1148215_ag_add x y) z;
  q1148215_ag_zero_left :
    forall x : A, q1148215_ag_add q1148215_ag_zero x = x;
  q1148215_ag_zero_right :
    forall x : A, q1148215_ag_add x q1148215_ag_zero = x;
  q1148215_ag_neg_left :
    forall x : A,
      q1148215_ag_add (q1148215_ag_neg x) x = q1148215_ag_zero;
  q1148215_ag_neg_right :
    forall x : A,
      q1148215_ag_add x (q1148215_ag_neg x) = q1148215_ag_zero;
  q1148215_ag_add_comm :
    forall x y : A, q1148215_ag_add x y = q1148215_ag_add y x
}.

Arguments q1148215_ag_zero {A} _.
Arguments q1148215_ag_add {A} _ _ _.
Arguments q1148215_ag_neg {A} _ _.

Record q1148215_preadditive (C : q1148215_category) : Type := {
  q1148215_hom_group :
    forall X Y : q1148215_obj C,
      q1148215_abelian_group (q1148215_hom C X Y);
  q1148215_comp_add_left :
    forall (W X Y : q1148215_obj C)
           (f g : q1148215_hom C W X)
           (h : q1148215_hom C X Y),
      q1148215_comp
        (q1148215_ag_add (q1148215_hom_group W X) f g) h =
      q1148215_ag_add (q1148215_hom_group W Y)
        (q1148215_comp f h) (q1148215_comp g h);
  q1148215_comp_add_right :
    forall (W X Y : q1148215_obj C)
           (f : q1148215_hom C W X)
           (g h : q1148215_hom C X Y),
      q1148215_comp f
        (q1148215_ag_add (q1148215_hom_group X Y) g h) =
      q1148215_ag_add (q1148215_hom_group W Y)
        (q1148215_comp f g) (q1148215_comp f h)
}.

Arguments q1148215_hom_group {C} _ _ _.

Definition q1148215_zero_morphism
    {C : q1148215_category}
    (P : q1148215_preadditive C)
    (X Y : q1148215_obj C) : q1148215_hom C X Y :=
  q1148215_ag_zero (q1148215_hom_group P X Y).

Definition q1148215_is_zero_object
    (C : q1148215_category) (Z : q1148215_obj C) : Prop :=
  (forall X : q1148215_obj C,
    exists f : q1148215_hom C Z X,
      forall g : q1148215_hom C Z X, g = f) /\
  (forall X : q1148215_obj C,
    exists f : q1148215_hom C X Z,
      forall g : q1148215_hom C X Z, g = f).

Definition q1148215_is_binary_biproduct
    {C : q1148215_category}
    (P : q1148215_preadditive C)
    (X Y B : q1148215_obj C)
    (inl : q1148215_hom C X B)
    (inr : q1148215_hom C Y B)
    (fst : q1148215_hom C B X)
    (snd : q1148215_hom C B Y) : Prop :=
  q1148215_comp inl fst = q1148215_id X /\
  q1148215_comp inr snd = q1148215_id Y /\
  q1148215_comp inl snd = q1148215_zero_morphism P X Y /\
  q1148215_comp inr fst = q1148215_zero_morphism P Y X /\
  q1148215_ag_add (q1148215_hom_group P B B)
    (q1148215_comp fst inl) (q1148215_comp snd inr) =
  q1148215_id B.

Record q1148215_additive_category
    (C : q1148215_category) : Type := {
  q1148215_add_preadditive : q1148215_preadditive C;
  q1148215_add_zero_object :
    exists Z : q1148215_obj C, q1148215_is_zero_object C Z;
  q1148215_add_biproduct :
    forall X Y : q1148215_obj C,
      exists B : q1148215_obj C,
      exists inl : q1148215_hom C X B,
      exists inr : q1148215_hom C Y B,
      exists fst : q1148215_hom C B X,
      exists snd : q1148215_hom C B Y,
        q1148215_is_binary_biproduct
          q1148215_add_preadditive X Y B inl inr fst snd
}.

Arguments q1148215_add_preadditive {C} _.

Definition q1148215_is_monomorphism
    {C : q1148215_category}
    {X Y : q1148215_obj C}
    (f : q1148215_hom C X Y) : Prop :=
  forall (Z : q1148215_obj C) (g h : q1148215_hom C Z X),
    q1148215_comp g f = q1148215_comp h f ->
    g = h.

Definition q1148215_is_epimorphism
    {C : q1148215_category}
    {X Y : q1148215_obj C}
    (f : q1148215_hom C X Y) : Prop :=
  forall (Z : q1148215_obj C) (g h : q1148215_hom C Y Z),
    q1148215_comp f g = q1148215_comp f h ->
    g = h.

Definition q1148215_is_kernel
    {C : q1148215_category}
    (P : q1148215_preadditive C)
    {X Y K : q1148215_obj C}
    (f : q1148215_hom C X Y)
    (k : q1148215_hom C K X) : Prop :=
  q1148215_comp k f = q1148215_zero_morphism P K Y /\
  forall (T : q1148215_obj C) (t : q1148215_hom C T X),
    q1148215_comp t f = q1148215_zero_morphism P T Y ->
    exists u : q1148215_hom C T K,
      q1148215_comp u k = t /\
      forall v : q1148215_hom C T K,
        q1148215_comp v k = t -> v = u.

Definition q1148215_is_cokernel
    {C : q1148215_category}
    (P : q1148215_preadditive C)
    {X Y Q : q1148215_obj C}
    (f : q1148215_hom C X Y)
    (q : q1148215_hom C Y Q) : Prop :=
  q1148215_comp f q = q1148215_zero_morphism P X Q /\
  forall (T : q1148215_obj C) (t : q1148215_hom C Y T),
    q1148215_comp f t = q1148215_zero_morphism P X T ->
    exists u : q1148215_hom C Q T,
      q1148215_comp q u = t /\
      forall v : q1148215_hom C Q T,
        q1148215_comp q v = t -> v = u.

Record q1148215_abelian_category
    (C : q1148215_category) : Type := {
  q1148215_ab_additive : q1148215_additive_category C;
  q1148215_ab_kernel :
    forall (X Y : q1148215_obj C) (f : q1148215_hom C X Y),
      exists K : q1148215_obj C,
      exists k : q1148215_hom C K X,
        q1148215_is_kernel
          (q1148215_add_preadditive q1148215_ab_additive) f k;
  q1148215_ab_cokernel :
    forall (X Y : q1148215_obj C) (f : q1148215_hom C X Y),
      exists Q : q1148215_obj C,
      exists q : q1148215_hom C Y Q,
        q1148215_is_cokernel
          (q1148215_add_preadditive q1148215_ab_additive) f q;
  q1148215_ab_mono_is_kernel :
    forall (X Y : q1148215_obj C) (m : q1148215_hom C X Y),
      q1148215_is_monomorphism m ->
      exists Z : q1148215_obj C,
      exists f : q1148215_hom C Y Z,
        q1148215_is_kernel
          (q1148215_add_preadditive q1148215_ab_additive) f m;
  q1148215_ab_epi_is_cokernel :
    forall (X Y : q1148215_obj C) (e : q1148215_hom C X Y),
      q1148215_is_epimorphism e ->
      exists Z : q1148215_obj C,
      exists f : q1148215_hom C Z X,
        q1148215_is_cokernel
          (q1148215_add_preadditive q1148215_ab_additive) f e
}.

Record q1148215_ring : Type := {
  q1148215_ring_carrier : Type;
  q1148215_ring_additive_group :
    q1148215_abelian_group q1148215_ring_carrier;
  q1148215_ring_one : q1148215_ring_carrier;
  q1148215_ring_mul :
    q1148215_ring_carrier ->
    q1148215_ring_carrier ->
    q1148215_ring_carrier;
  q1148215_ring_mul_assoc :
    forall x y z : q1148215_ring_carrier,
      q1148215_ring_mul x (q1148215_ring_mul y z) =
      q1148215_ring_mul (q1148215_ring_mul x y) z;
  q1148215_ring_one_left :
    forall x : q1148215_ring_carrier,
      q1148215_ring_mul q1148215_ring_one x = x;
  q1148215_ring_one_right :
    forall x : q1148215_ring_carrier,
      q1148215_ring_mul x q1148215_ring_one = x;
  q1148215_ring_mul_add_left :
    forall x y z : q1148215_ring_carrier,
      q1148215_ring_mul x
        (q1148215_ag_add q1148215_ring_additive_group y z) =
      q1148215_ag_add q1148215_ring_additive_group
        (q1148215_ring_mul x y) (q1148215_ring_mul x z);
  q1148215_ring_mul_add_right :
    forall x y z : q1148215_ring_carrier,
      q1148215_ring_mul
        (q1148215_ag_add q1148215_ring_additive_group x y) z =
      q1148215_ag_add q1148215_ring_additive_group
        (q1148215_ring_mul x z) (q1148215_ring_mul y z)
}.

Arguments q1148215_ring_carrier _ : clear implicits.
Arguments q1148215_ring_additive_group _.
Arguments q1148215_ring_one {q}.
Arguments q1148215_ring_mul {q} _ _.

Record q1148215_module (R : q1148215_ring) : Type := {
  q1148215_module_carrier : Type;
  q1148215_module_additive_group :
    q1148215_abelian_group q1148215_module_carrier;
  q1148215_smul :
    q1148215_ring_carrier R ->
    q1148215_module_carrier ->
    q1148215_module_carrier;
  q1148215_smul_one :
    forall x : q1148215_module_carrier,
      q1148215_smul (q1148215_ring_one (q := R)) x = x;
  q1148215_smul_mul :
    forall (a b : q1148215_ring_carrier R)
           (x : q1148215_module_carrier),
      q1148215_smul (q1148215_ring_mul a b) x =
      q1148215_smul a (q1148215_smul b x);
  q1148215_smul_add_scalar :
    forall (a b : q1148215_ring_carrier R)
           (x : q1148215_module_carrier),
      q1148215_smul
        (q1148215_ag_add (q1148215_ring_additive_group R) a b) x =
      q1148215_ag_add q1148215_module_additive_group
        (q1148215_smul a x) (q1148215_smul b x);
  q1148215_smul_add_vector :
    forall (a : q1148215_ring_carrier R)
           (x y : q1148215_module_carrier),
      q1148215_smul a
        (q1148215_ag_add q1148215_module_additive_group x y) =
      q1148215_ag_add q1148215_module_additive_group
        (q1148215_smul a x) (q1148215_smul a y)
}.

Arguments q1148215_module_carrier {R} _.
Arguments q1148215_module_additive_group {R} _.
Arguments q1148215_smul {R} {q} _ _.

Definition q1148215_is_linear
    {R : q1148215_ring}
    (M N : q1148215_module R)
    (f : q1148215_module_carrier M ->
         q1148215_module_carrier N) : Prop :=
  (forall x y : q1148215_module_carrier M,
    f (q1148215_ag_add (q1148215_module_additive_group M) x y) =
    q1148215_ag_add (q1148215_module_additive_group N) (f x) (f y)) /\
  (forall (a : q1148215_ring_carrier R)
          (x : q1148215_module_carrier M),
    f (q1148215_smul a x) = q1148215_smul a (f x)).

Record q1148215_module_functor
    (C : q1148215_category) (R : q1148215_ring) : Type := {
  q1148215_fobj :
    q1148215_obj C -> q1148215_module R;
  q1148215_fmap :
    forall X Y : q1148215_obj C,
      q1148215_hom C X Y ->
      q1148215_module_carrier (q1148215_fobj X) ->
      q1148215_module_carrier (q1148215_fobj Y);
  q1148215_fmap_linear :
    forall (X Y : q1148215_obj C) (f : q1148215_hom C X Y),
      q1148215_is_linear (q1148215_fobj X) (q1148215_fobj Y)
        (q1148215_fmap X Y f);
  q1148215_fmap_id :
    forall (X : q1148215_obj C)
           (x : q1148215_module_carrier (q1148215_fobj X)),
      q1148215_fmap X X (q1148215_id X) x = x;
  q1148215_fmap_comp :
    forall (X Y Z : q1148215_obj C)
           (f : q1148215_hom C X Y)
           (g : q1148215_hom C Y Z)
           (x : q1148215_module_carrier (q1148215_fobj X)),
      q1148215_fmap X Z (q1148215_comp f g) x =
      q1148215_fmap Y Z g (q1148215_fmap X Y f x)
}.

Arguments q1148215_fobj {C R} _ _.
Arguments q1148215_fmap {C R} _ {X Y} _ _.

Definition q1148215_functor_full
    {C : q1148215_category}
    {R : q1148215_ring}
    (F : q1148215_module_functor C R) : Prop :=
  forall (X Y : q1148215_obj C)
         (f : q1148215_module_carrier (q1148215_fobj F X) ->
              q1148215_module_carrier (q1148215_fobj F Y)),
    q1148215_is_linear (q1148215_fobj F X) (q1148215_fobj F Y) f ->
    exists g : q1148215_hom C X Y,
      forall x : q1148215_module_carrier (q1148215_fobj F X),
        q1148215_fmap F g x = f x.

Definition q1148215_functor_faithful
    {C : q1148215_category}
    {R : q1148215_ring}
    (F : q1148215_module_functor C R) : Prop :=
  forall (X Y : q1148215_obj C) (f g : q1148215_hom C X Y),
    (forall x : q1148215_module_carrier (q1148215_fobj F X),
      q1148215_fmap F f x = q1148215_fmap F g x) ->
    f = g.

Record q1148215_finite_category
    (J : q1148215_category) : Type := {
  q1148215_finite_objects : list (q1148215_obj J);
  q1148215_finite_objects_complete :
    forall j : q1148215_obj J, In j q1148215_finite_objects;
  q1148215_finite_morphisms :
    forall i j : q1148215_obj J,
      list (q1148215_hom J i j);
  q1148215_finite_morphisms_complete :
    forall (i j : q1148215_obj J) (f : q1148215_hom J i j),
      In f (q1148215_finite_morphisms i j)
}.

Record q1148215_diagram
    (J C : q1148215_category) : Type := {
  q1148215_dobj :
    q1148215_obj J -> q1148215_obj C;
  q1148215_dmap :
    forall i j : q1148215_obj J,
      q1148215_hom J i j ->
      q1148215_hom C (q1148215_dobj i) (q1148215_dobj j);
  q1148215_dmap_id :
    forall i : q1148215_obj J,
      q1148215_dmap i i (q1148215_id i) =
      q1148215_id (q1148215_dobj i);
  q1148215_dmap_comp :
    forall (i j k : q1148215_obj J)
           (f : q1148215_hom J i j)
           (g : q1148215_hom J j k),
      q1148215_dmap i k (q1148215_comp f g) =
      q1148215_comp (q1148215_dmap i j f) (q1148215_dmap j k g)
}.

Arguments q1148215_dobj {J C} _ _.
Arguments q1148215_dmap {J C} _ {i j} _.

Record q1148215_cone
    {J C : q1148215_category}
    (D : q1148215_diagram J C) : Type := {
  q1148215_cone_apex : q1148215_obj C;
  q1148215_cone_leg :
    forall j : q1148215_obj J,
      q1148215_hom C q1148215_cone_apex (q1148215_dobj D j);
  q1148215_cone_natural :
    forall (i j : q1148215_obj J) (f : q1148215_hom J i j),
      q1148215_comp (q1148215_cone_leg i) (q1148215_dmap D f) =
      q1148215_cone_leg j
}.

Arguments q1148215_cone_apex {J C D} _.
Arguments q1148215_cone_leg {J C D} _ _.

Definition q1148215_is_limit
    {J C : q1148215_category}
    {D : q1148215_diagram J C}
    (K : q1148215_cone D) : Prop :=
  forall (X : q1148215_obj C)
         (leg : forall j : q1148215_obj J,
           q1148215_hom C X (q1148215_dobj D j)),
    (forall (i j : q1148215_obj J) (f : q1148215_hom J i j),
      q1148215_comp (leg i) (q1148215_dmap D f) = leg j) ->
    exists u : q1148215_hom C X (q1148215_cone_apex K),
      (forall j : q1148215_obj J,
        q1148215_comp u (q1148215_cone_leg K j) = leg j) /\
      forall v : q1148215_hom C X (q1148215_cone_apex K),
        (forall j : q1148215_obj J,
          q1148215_comp v (q1148215_cone_leg K j) = leg j) ->
        v = u.

Record q1148215_cocone
    {J C : q1148215_category}
    (D : q1148215_diagram J C) : Type := {
  q1148215_cocone_apex : q1148215_obj C;
  q1148215_cocone_leg :
    forall j : q1148215_obj J,
      q1148215_hom C (q1148215_dobj D j) q1148215_cocone_apex;
  q1148215_cocone_natural :
    forall (i j : q1148215_obj J) (f : q1148215_hom J i j),
      q1148215_comp (q1148215_dmap D f) (q1148215_cocone_leg j) =
      q1148215_cocone_leg i
}.

Arguments q1148215_cocone_apex {J C D} _.
Arguments q1148215_cocone_leg {J C D} _ _.

Definition q1148215_is_colimit
    {J C : q1148215_category}
    {D : q1148215_diagram J C}
    (K : q1148215_cocone D) : Prop :=
  forall (X : q1148215_obj C)
         (leg : forall j : q1148215_obj J,
           q1148215_hom C (q1148215_dobj D j) X),
    (forall (i j : q1148215_obj J) (f : q1148215_hom J i j),
      q1148215_comp (q1148215_dmap D f) (leg j) = leg i) ->
    exists u : q1148215_hom C (q1148215_cocone_apex K) X,
      (forall j : q1148215_obj J,
        q1148215_comp (q1148215_cocone_leg K j) u = leg j) /\
      forall v : q1148215_hom C (q1148215_cocone_apex K) X,
        (forall j : q1148215_obj J,
          q1148215_comp (q1148215_cocone_leg K j) v = leg j) ->
        v = u.

Definition q1148215_mapped_cone_is_limit
    {J C : q1148215_category}
    {R : q1148215_ring}
    (F : q1148215_module_functor C R)
    (D : q1148215_diagram J C)
    (K : q1148215_cone D) : Prop :=
  forall (M : q1148215_module R)
         (leg : forall j : q1148215_obj J,
           q1148215_module_carrier M ->
           q1148215_module_carrier
             (q1148215_fobj F (q1148215_dobj D j))),
    (forall j : q1148215_obj J,
      q1148215_is_linear M
        (q1148215_fobj F (q1148215_dobj D j)) (leg j)) ->
    (forall (i j : q1148215_obj J)
            (f : q1148215_hom J i j)
            (x : q1148215_module_carrier M),
      q1148215_fmap F (q1148215_dmap D f) (leg i x) = leg j x) ->
    exists u :
      q1148215_module_carrier M ->
      q1148215_module_carrier
        (q1148215_fobj F (q1148215_cone_apex K)),
      q1148215_is_linear M
        (q1148215_fobj F (q1148215_cone_apex K)) u /\
      (forall (j : q1148215_obj J)
              (x : q1148215_module_carrier M),
        q1148215_fmap F (q1148215_cone_leg K j) (u x) = leg j x) /\
      forall v :
        q1148215_module_carrier M ->
        q1148215_module_carrier
          (q1148215_fobj F (q1148215_cone_apex K)),
        q1148215_is_linear M
          (q1148215_fobj F (q1148215_cone_apex K)) v ->
        (forall (j : q1148215_obj J)
                (x : q1148215_module_carrier M),
          q1148215_fmap F (q1148215_cone_leg K j) (v x) = leg j x) ->
        forall x : q1148215_module_carrier M, v x = u x.

Definition q1148215_mapped_cocone_is_colimit
    {J C : q1148215_category}
    {R : q1148215_ring}
    (F : q1148215_module_functor C R)
    (D : q1148215_diagram J C)
    (K : q1148215_cocone D) : Prop :=
  forall (M : q1148215_module R)
         (leg : forall j : q1148215_obj J,
           q1148215_module_carrier
             (q1148215_fobj F (q1148215_dobj D j)) ->
           q1148215_module_carrier M),
    (forall j : q1148215_obj J,
      q1148215_is_linear
        (q1148215_fobj F (q1148215_dobj D j)) M (leg j)) ->
    (forall (i j : q1148215_obj J)
            (f : q1148215_hom J i j)
            (x : q1148215_module_carrier
              (q1148215_fobj F (q1148215_dobj D i))),
      leg j (q1148215_fmap F (q1148215_dmap D f) x) = leg i x) ->
    exists u :
      q1148215_module_carrier
        (q1148215_fobj F (q1148215_cocone_apex K)) ->
      q1148215_module_carrier M,
      q1148215_is_linear
        (q1148215_fobj F (q1148215_cocone_apex K)) M u /\
      (forall (j : q1148215_obj J)
              (x : q1148215_module_carrier
                (q1148215_fobj F (q1148215_dobj D j))),
        u (q1148215_fmap F (q1148215_cocone_leg K j) x) = leg j x) /\
      forall v :
        q1148215_module_carrier
          (q1148215_fobj F (q1148215_cocone_apex K)) ->
        q1148215_module_carrier M,
        q1148215_is_linear
          (q1148215_fobj F (q1148215_cocone_apex K)) M v ->
        (forall (j : q1148215_obj J)
                (x : q1148215_module_carrier
                  (q1148215_fobj F (q1148215_dobj D j))),
          v (q1148215_fmap F (q1148215_cocone_leg K j) x) = leg j x) ->
        forall x :
          q1148215_module_carrier
            (q1148215_fobj F (q1148215_cocone_apex K)),
          v x = u x.

Definition q1148215_preserves_finite_limits
    {C : q1148215_category}
    {R : q1148215_ring}
    (F : q1148215_module_functor C R) : Prop :=
  forall (J : q1148215_category)
         (_ : q1148215_finite_category J)
         (D : q1148215_diagram J C)
         (K : q1148215_cone D),
    q1148215_is_limit K ->
    q1148215_mapped_cone_is_limit F (D := D) K.

Definition q1148215_preserves_finite_colimits
    {C : q1148215_category}
    {R : q1148215_ring}
    (F : q1148215_module_functor C R) : Prop :=
  forall (J : q1148215_category)
         (_ : q1148215_finite_category J)
         (D : q1148215_diagram J C)
         (K : q1148215_cocone D),
    q1148215_is_colimit K ->
    q1148215_mapped_cocone_is_colimit F (D := D) K.

Theorem CategoryTheory_Abelian_freyd_mitchell :
  forall (C : q1148215_category),
    q1148215_abelian_category C ->
    exists R : q1148215_ring,
    exists F : q1148215_module_functor C R,
      q1148215_functor_full F /\
      q1148215_functor_faithful F /\
      q1148215_preserves_finite_limits F /\
      q1148215_preserves_finite_colimits F.
Admitted.
