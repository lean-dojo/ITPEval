(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1259814
  (thousand-theorems__rocq__Q1259814), "Nielsen–Schreier theorem": every
  subgroup of an arbitrary free group is itself a free group. This file
  contains no proof.
*)

Set Universe Polymorphism.
Unset Implicit Arguments.

Polymorphic Record q1259814_group@{u} : Type@{u+1} := {
  q1259814_carrier : Type@{u};
  q1259814_one : q1259814_carrier;
  q1259814_mul :
    q1259814_carrier -> q1259814_carrier -> q1259814_carrier;
  q1259814_inv : q1259814_carrier -> q1259814_carrier;
  q1259814_mul_assoc :
    forall x y z : q1259814_carrier,
      q1259814_mul x (q1259814_mul y z) =
      q1259814_mul (q1259814_mul x y) z;
  q1259814_one_mul :
    forall x : q1259814_carrier, q1259814_mul q1259814_one x = x;
  q1259814_mul_one :
    forall x : q1259814_carrier, q1259814_mul x q1259814_one = x;
  q1259814_inv_mul :
    forall x : q1259814_carrier,
      q1259814_mul (q1259814_inv x) x = q1259814_one;
  q1259814_mul_inv :
    forall x : q1259814_carrier,
      q1259814_mul x (q1259814_inv x) = q1259814_one
}.

Arguments q1259814_carrier _ : clear implicits.
Arguments q1259814_one {q}.
Arguments q1259814_mul {q} _ _.
Arguments q1259814_inv {q} _.

Polymorphic Record q1259814_subgroup@{u}
    (G : q1259814_group@{u}) : Type@{u+1} := {
  q1259814_member : q1259814_carrier G -> Prop;
  q1259814_subgroup_one : q1259814_member q1259814_one;
  q1259814_subgroup_mul :
    forall x y : q1259814_carrier G,
      q1259814_member x ->
      q1259814_member y ->
      q1259814_member (q1259814_mul x y);
  q1259814_subgroup_inv :
    forall x : q1259814_carrier G,
      q1259814_member x ->
      q1259814_member (q1259814_inv x)
}.

Arguments q1259814_member {G} _ _.
Arguments q1259814_subgroup_one {G} _.
Arguments q1259814_subgroup_mul {G} _ _ _ _ _.
Arguments q1259814_subgroup_inv {G} _ _ _.

Polymorphic Definition q1259814_group_homomorphism@{u}
    (G K : q1259814_group@{u})
    (f : q1259814_carrier G -> q1259814_carrier K) : Prop :=
  f q1259814_one = q1259814_one /\
  forall x y : q1259814_carrier G,
    f (q1259814_mul x y) = q1259814_mul (f x) (f y).

(* Coherence makes maps from the inherited subgroup independent of the
   particular proofs that their arguments belong to the subgroup. *)
Polymorphic Record q1259814_subgroup_map@{u}
    (G : q1259814_group@{u})
    (H : q1259814_subgroup@{u} G)
    (K : q1259814_group@{u}) : Type@{u+1} := {
  q1259814_subgroup_map_apply :
    forall x : q1259814_carrier G,
      q1259814_member H x -> q1259814_carrier K;
  q1259814_subgroup_map_coherent :
    forall (x : q1259814_carrier G)
           (hx hy : q1259814_member H x),
      q1259814_subgroup_map_apply x hx =
      q1259814_subgroup_map_apply x hy
}.

Polymorphic Definition q1259814_subgroup_homomorphism@{u}
    (G : q1259814_group@{u})
    (H : q1259814_subgroup@{u} G)
    (K : q1259814_group@{u})
    (f : q1259814_subgroup_map@{u} G H K) : Prop :=
  @q1259814_subgroup_map_apply
    G H K f q1259814_one (q1259814_subgroup_one H) =
    q1259814_one /\
  forall (x y : q1259814_carrier G)
         (hx : q1259814_member H x)
         (hy : q1259814_member H y),
    @q1259814_subgroup_map_apply
      G H K f
      (q1259814_mul x y)
      (q1259814_subgroup_mul H x y hx hy) =
    q1259814_mul
      (@q1259814_subgroup_map_apply G H K f x hx)
      (@q1259814_subgroup_map_apply G H K f y hy).

Polymorphic Definition q1259814_is_free_group@{u}
    (G : q1259814_group@{u}) : Prop :=
  exists X : Type@{u},
  exists generators : X -> q1259814_carrier G,
  forall (K : q1259814_group@{u})
         (label : X -> q1259814_carrier K),
    exists lift : q1259814_carrier G -> q1259814_carrier K,
      q1259814_group_homomorphism@{u} G K lift /\
      (forall x : X, lift (generators x) = label x) /\
      (forall other : q1259814_carrier G -> q1259814_carrier K,
        q1259814_group_homomorphism@{u} G K other ->
        (forall x : X, other (generators x) = label x) ->
        forall g : q1259814_carrier G, other g = lift g).

Polymorphic Definition q1259814_is_free_subgroup@{u}
    (G : q1259814_group@{u})
    (H : q1259814_subgroup@{u} G) : Prop :=
  exists X : Type@{u},
  exists generators : X -> q1259814_carrier G,
  exists generators_mem :
    forall x : X, q1259814_member H (generators x),
  forall (K : q1259814_group@{u})
         (label : X -> q1259814_carrier K),
    exists lift : q1259814_subgroup_map@{u} G H K,
      q1259814_subgroup_homomorphism@{u} G H K lift /\
      (forall x : X,
        @q1259814_subgroup_map_apply
          G H K lift (generators x) (generators_mem x) =
        label x) /\
      (forall other : q1259814_subgroup_map@{u} G H K,
        q1259814_subgroup_homomorphism@{u} G H K other ->
        (forall x : X,
          @q1259814_subgroup_map_apply
            G H K other (generators x) (generators_mem x) =
          label x) ->
        forall (h : q1259814_carrier G)
               (hh_other hh_lift : q1259814_member H h),
          @q1259814_subgroup_map_apply G H K other h hh_other =
          @q1259814_subgroup_map_apply G H K lift h hh_lift).

Polymorphic Theorem subgroupIsFreeOfIsFree@{u} :
  forall (G : q1259814_group@{u})
         (H : q1259814_subgroup@{u} G),
    q1259814_is_free_group@{u} G ->
    q1259814_is_free_subgroup@{u} G H.
Admitted.
