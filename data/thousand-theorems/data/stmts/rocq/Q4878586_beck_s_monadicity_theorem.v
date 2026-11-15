(*
  Statement-only formalization of Thousand Theorems corpus artifact Q4878586
  (thousand-theorems__rocq__Q4878586), "Beck's monadicity theorem": a right
  adjoint that creates coequalizers of all pairs split by that right adjoint
  is monadic. This file contains no proof.
*)

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.

Record q4878586_category (Object : Type) : Type := {
  q4878586_hom : Object -> Object -> Type;
  q4878586_id :
    forall X : Object, q4878586_hom X X;
  q4878586_comp :
    forall X Y Z : Object,
      q4878586_hom X Y ->
      q4878586_hom Y Z ->
      q4878586_hom X Z;
  q4878586_comp_id_left :
    forall (X Y : Object) (f : q4878586_hom X Y),
      q4878586_comp (q4878586_id X) f = f;
  q4878586_comp_id_right :
    forall (X Y : Object) (f : q4878586_hom X Y),
      q4878586_comp f (q4878586_id Y) = f;
  q4878586_comp_assoc :
    forall (W X Y Z : Object)
           (f : q4878586_hom W X)
           (g : q4878586_hom X Y)
           (h : q4878586_hom Y Z),
      q4878586_comp (q4878586_comp f g) h =
      q4878586_comp f (q4878586_comp g h)
}.

Arguments q4878586_hom {Object} _ _ _.
Arguments q4878586_id {Object q} _.
Arguments q4878586_comp {Object q X Y Z} _ _.

Record q4878586_functor
    {CObject DObject : Type}
    (C : q4878586_category CObject)
    (D : q4878586_category DObject) : Type := {
  q4878586_fobj : CObject -> DObject;
  q4878586_fmap :
    forall X Y : CObject,
      q4878586_hom C X Y ->
      q4878586_hom D (q4878586_fobj X) (q4878586_fobj Y);
  q4878586_fmap_id :
    forall X : CObject,
      q4878586_fmap X X (q4878586_id X) =
      q4878586_id (q4878586_fobj X);
  q4878586_fmap_comp :
    forall (X Y Z : CObject)
           (f : q4878586_hom C X Y)
           (g : q4878586_hom C Y Z),
      q4878586_fmap X Z (q4878586_comp f g) =
      q4878586_comp
        (q4878586_fmap X Y f)
        (q4878586_fmap Y Z g)
}.

Arguments q4878586_fobj
  {CObject DObject C D} _ _.
Arguments q4878586_fmap
  {CObject DObject C D} _ {X Y} _.

Record q4878586_iso
    {Object : Type}
    (C : q4878586_category Object)
    (X Y : Object) : Type := {
  q4878586_iso_hom : q4878586_hom C X Y;
  q4878586_iso_inv : q4878586_hom C Y X;
  q4878586_iso_inv_hom :
    q4878586_comp q4878586_iso_hom q4878586_iso_inv =
    q4878586_id X;
  q4878586_iso_hom_inv :
    q4878586_comp q4878586_iso_inv q4878586_iso_hom =
    q4878586_id Y
}.

Arguments q4878586_iso_hom {Object C X Y} _.
Arguments q4878586_iso_inv {Object C X Y} _.

Record q4878586_is_coequalizer
    {Object : Type}
    (C : q4878586_category Object)
    {A B Q : Object}
    (f g : q4878586_hom C A B)
    (quotient : q4878586_hom C B Q) : Type := {
  q4878586_coequalizer_condition :
    q4878586_comp f quotient = q4878586_comp g quotient;
  q4878586_coequalizer_desc :
    forall (X : Object) (candidate : q4878586_hom C B X),
      q4878586_comp f candidate = q4878586_comp g candidate ->
      q4878586_hom C Q X;
  q4878586_coequalizer_fac :
    forall (X : Object) (candidate : q4878586_hom C B X)
           (condition :
             q4878586_comp f candidate =
             q4878586_comp g candidate),
      q4878586_comp quotient
        (q4878586_coequalizer_desc X candidate condition) =
      candidate;
  q4878586_coequalizer_uniq :
    forall (X : Object) (candidate : q4878586_hom C B X)
           (condition :
             q4878586_comp f candidate =
             q4878586_comp g candidate)
           (other : q4878586_hom C Q X),
      q4878586_comp quotient other = candidate ->
      other = q4878586_coequalizer_desc X candidate condition
}.

Record q4878586_split_coequalizer
    {Object : Type}
    (C : q4878586_category Object)
    {A B : Object}
    (f g : q4878586_hom C A B) : Type := {
  q4878586_split_object : Object;
  q4878586_split_quotient :
    q4878586_hom C B q4878586_split_object;
  q4878586_split_section :
    q4878586_hom C q4878586_split_object B;
  q4878586_splitting : q4878586_hom C B A;
  q4878586_split_coequalizes :
    q4878586_comp f q4878586_split_quotient =
    q4878586_comp g q4878586_split_quotient;
  q4878586_split_quotient_section :
    q4878586_comp q4878586_split_section q4878586_split_quotient =
    q4878586_id q4878586_split_object;
  q4878586_split_bottom :
    q4878586_comp q4878586_splitting g =
    q4878586_id B;
  q4878586_split_top :
    q4878586_comp q4878586_splitting f =
    q4878586_comp q4878586_split_quotient q4878586_split_section
}.

Arguments q4878586_split_object
  {Object C A B f g} _.
Arguments q4878586_split_quotient
  {Object C A B f g} _.

Definition q4878586_is_G_split_pair
    {CObject DObject : Type}
    (C : q4878586_category CObject)
    (D : q4878586_category DObject)
    (G : q4878586_functor D C)
    {A B : DObject}
    (f g : q4878586_hom D A B) : Prop :=
  exists split :
      q4878586_split_coequalizer C
        (q4878586_fmap G f) (q4878586_fmap G g),
    True.

Record q4878586_liftable_coequalizer
    {CObject DObject : Type}
    (C : q4878586_category CObject)
    (D : q4878586_category DObject)
    (G : q4878586_functor D C)
    {A B : DObject}
    (f g : q4878586_hom D A B)
    {Q : CObject}
    (quotient :
      q4878586_hom C (q4878586_fobj G B) Q) : Type := {
  q4878586_lifted_object : DObject;
  q4878586_lifted_quotient :
    q4878586_hom D B q4878586_lifted_object;
  q4878586_lifted_condition :
    q4878586_comp f q4878586_lifted_quotient =
    q4878586_comp g q4878586_lifted_quotient;
  q4878586_lifted_comparison :
    q4878586_iso C
      (q4878586_fobj G q4878586_lifted_object) Q;
  q4878586_lifted_quotient_maps_to_original :
    q4878586_comp
      (q4878586_fmap G q4878586_lifted_quotient)
      (q4878586_iso_hom q4878586_lifted_comparison) =
    quotient
}.

Record q4878586_creates_coequalizer
    {CObject DObject : Type}
    (C : q4878586_category CObject)
    (D : q4878586_category DObject)
    (G : q4878586_functor D C)
    {A B : DObject}
    (f g : q4878586_hom D A B) : Type := {
  q4878586_reflects_coequalizer :
    forall (Q : DObject) (q : q4878586_hom D B Q),
      q4878586_comp f q = q4878586_comp g q ->
      q4878586_is_coequalizer C
        (q4878586_fmap G f)
        (q4878586_fmap G g)
        (q4878586_fmap G q) ->
      inhabited (q4878586_is_coequalizer D f g q);
  q4878586_lifts_coequalizer :
    forall (Q : CObject)
           (q : q4878586_hom C (q4878586_fobj G B) Q),
      q4878586_is_coequalizer C
        (q4878586_fmap G f)
        (q4878586_fmap G g) q ->
      @q4878586_liftable_coequalizer
        CObject DObject C D G A B f g Q q
}.

Definition q4878586_creates_G_split_coequalizers
    {CObject DObject : Type}
    (C : q4878586_category CObject)
    (D : q4878586_category DObject)
    (G : q4878586_functor D C) : Type :=
  forall (A B : DObject)
         (f g : q4878586_hom D A B)
         (_ :
           @q4878586_is_G_split_pair
             CObject DObject C D G A B f g),
    @q4878586_creates_coequalizer
      CObject DObject C D G A B f g.

Record q4878586_adjunction
    {CObject DObject : Type}
    (C : q4878586_category CObject)
    (D : q4878586_category DObject)
    (F : q4878586_functor C D)
    (G : q4878586_functor D C) : Type := {
  q4878586_unit :
    forall X : CObject,
      q4878586_hom C X
        (q4878586_fobj G (q4878586_fobj F X));
  q4878586_unit_natural :
    forall (X Y : CObject) (f : q4878586_hom C X Y),
      q4878586_comp
        (q4878586_unit X)
        (q4878586_fmap G (q4878586_fmap F f)) =
      q4878586_comp f (q4878586_unit Y);
  q4878586_counit :
    forall Y : DObject,
      q4878586_hom D
        (q4878586_fobj F (q4878586_fobj G Y)) Y;
  q4878586_counit_natural :
    forall (Y Z : DObject) (f : q4878586_hom D Y Z),
      q4878586_comp
        (q4878586_fmap F (q4878586_fmap G f))
        (q4878586_counit Z) =
      q4878586_comp (q4878586_counit Y) f;
  q4878586_left_triangle :
    forall X : CObject,
      q4878586_comp
        (q4878586_fmap F (q4878586_unit X))
        (q4878586_counit (q4878586_fobj F X)) =
      q4878586_id (q4878586_fobj F X);
  q4878586_right_triangle :
    forall Y : DObject,
      q4878586_comp
        (q4878586_unit (q4878586_fobj G Y))
        (q4878586_fmap G (q4878586_counit Y)) =
      q4878586_id (q4878586_fobj G Y)
}.

Arguments q4878586_unit
  {CObject DObject C D F G} _ _.
Arguments q4878586_counit
  {CObject DObject C D F G} _ _.

Record q4878586_algebra
    {CObject DObject : Type}
    {C : q4878586_category CObject}
    {D : q4878586_category DObject}
    {F : q4878586_functor C D}
    {G : q4878586_functor D C}
    (adj : @q4878586_adjunction CObject DObject C D F G) : Type := {
  q4878586_algebra_carrier : CObject;
  q4878586_algebra_action :
    q4878586_hom C
      (q4878586_fobj G (q4878586_fobj F q4878586_algebra_carrier))
      q4878586_algebra_carrier;
  q4878586_algebra_unit :
    q4878586_comp
      (q4878586_unit adj q4878586_algebra_carrier)
      q4878586_algebra_action =
    q4878586_id q4878586_algebra_carrier;
  q4878586_algebra_assoc :
    q4878586_comp
      (q4878586_fmap G
        (q4878586_fmap F q4878586_algebra_action))
      q4878586_algebra_action =
    q4878586_comp
      (q4878586_fmap G
        (q4878586_counit adj
          (q4878586_fobj F q4878586_algebra_carrier)))
      q4878586_algebra_action
}.

Arguments q4878586_algebra_carrier
  {CObject DObject C D F G adj} _.
Arguments q4878586_algebra_action
  {CObject DObject C D F G adj} _.

Definition q4878586_comparison_hom
    {CObject DObject : Type}
    {C : q4878586_category CObject}
    {D : q4878586_category DObject}
    {F : q4878586_functor C D}
    {G : q4878586_functor D C}
    (adj : @q4878586_adjunction CObject DObject C D F G)
    (A B : DObject)
    (f :
      q4878586_hom C
        (q4878586_fobj G A) (q4878586_fobj G B)) : Prop :=
  q4878586_comp
    (q4878586_fmap G (q4878586_counit adj A)) f =
  q4878586_comp
    (q4878586_fmap G (q4878586_fmap F f))
    (q4878586_fmap G (q4878586_counit adj B)).

Definition q4878586_algebra_iso_to_comparison
    {CObject DObject : Type}
    {C : q4878586_category CObject}
    {D : q4878586_category DObject}
    {F : q4878586_functor C D}
    {G : q4878586_functor D C}
    (adj : @q4878586_adjunction CObject DObject C D F G)
    (A : q4878586_algebra adj)
    (Y : DObject) : Prop :=
  exists forward :
      q4878586_hom C
        (q4878586_algebra_carrier A) (q4878586_fobj G Y),
    exists backward :
      q4878586_hom C
        (q4878586_fobj G Y) (q4878586_algebra_carrier A),
      q4878586_comp
        (q4878586_algebra_action A)
        forward =
      q4878586_comp
        (q4878586_fmap G (q4878586_fmap F forward))
        (q4878586_fmap G (q4878586_counit adj Y)) /\
      q4878586_comp
        (q4878586_fmap G (q4878586_counit adj Y))
        backward =
      q4878586_comp
        (q4878586_fmap G (q4878586_fmap F backward))
        (q4878586_algebra_action A) /\
      q4878586_comp forward backward =
        q4878586_id (q4878586_algebra_carrier A) /\
      q4878586_comp backward forward =
        q4878586_id (q4878586_fobj G Y).

Record q4878586_comparison_is_equivalence
    {CObject DObject : Type}
    (C : q4878586_category CObject)
    (D : q4878586_category DObject)
    (F : q4878586_functor C D)
    (G : q4878586_functor D C)
    (adj : @q4878586_adjunction CObject DObject C D F G) : Prop := {
  q4878586_comparison_faithful :
    forall (A B : DObject)
           (f g : q4878586_hom D A B),
      q4878586_fmap G f = q4878586_fmap G g ->
      f = g;
  q4878586_comparison_full :
    forall (A B : DObject)
           (f :
             q4878586_hom C
               (q4878586_fobj G A) (q4878586_fobj G B)),
      q4878586_comparison_hom adj A B f ->
      exists lift : q4878586_hom D A B,
        q4878586_fmap G lift = f;
  q4878586_comparison_essentially_surjective :
    forall A : q4878586_algebra adj,
      exists Y : DObject,
        @q4878586_algebra_iso_to_comparison
          CObject DObject C D F G adj A Y
}.

Record q4878586_monadic_right_adjoint
    {CObject DObject : Type}
    (C : q4878586_category CObject)
    (D : q4878586_category DObject)
    (G : q4878586_functor D C) : Type := {
  q4878586_left_adjoint : q4878586_functor C D;
  q4878586_monadic_adjunction :
    @q4878586_adjunction
      CObject DObject C D q4878586_left_adjoint G;
  q4878586_monadic_comparison :
    @q4878586_comparison_is_equivalence
      CObject DObject C D q4878586_left_adjoint G
      q4878586_monadic_adjunction
}.

Theorem CategoryTheory_Monad_monadicOfCreatesGSplitCoequalizers :
  forall (CObject DObject : Type)
         (C : q4878586_category CObject)
         (D : q4878586_category DObject)
         (G : q4878586_functor D C)
         (F : q4878586_functor C D),
    @q4878586_adjunction CObject DObject C D F G ->
    @q4878586_creates_G_split_coequalizers CObject DObject C D G ->
    @q4878586_monadic_right_adjoint CObject DObject C D G.
Admitted.
