(*
  Statement-only formalization of Thousand Theorems corpus artifact Q245098
  (thousand-theorems__rocq__Q245098), "Intermediate value theorem": a
  continuous function on a closed interval in a densely ordered conditionally
  complete linear order takes every value between its endpoint values. This
  file contains no proof.
*)

Set Universe Polymorphism.
Set Implicit Arguments.

Definition q245098_set (X : Type) : Type := X -> Prop.

Definition q245098_subset
    {X : Type}
    (U V : q245098_set X) : Prop :=
  forall x : X, U x -> V x.

Record q245098_linear_order (X : Type) : Type := {
  q245098_le : X -> X -> Prop;
  q245098_le_refl :
    forall x : X, q245098_le x x;
  q245098_le_antisym :
    forall x y : X,
      q245098_le x y -> q245098_le y x -> x = y;
  q245098_le_trans :
    forall x y z : X,
      q245098_le x y -> q245098_le y z -> q245098_le x z;
  q245098_le_total :
    forall x y : X, q245098_le x y \/ q245098_le y x
}.

Arguments q245098_le {X} _ _ _.

Definition q245098_lt
    {X : Type}
    (O : q245098_linear_order X)
    (x y : X) : Prop :=
  q245098_le O x y /\ ~ q245098_le O y x.

Definition q245098_nonempty
    {X : Type}
    (s : q245098_set X) : Prop :=
  exists x : X, s x.

Definition q245098_bounded_above
    {X : Type}
    (O : q245098_linear_order X)
    (s : q245098_set X) : Prop :=
  exists upper : X,
    forall x : X, s x -> q245098_le O x upper.

Definition q245098_bounded_below
    {X : Type}
    (O : q245098_linear_order X)
    (s : q245098_set X) : Prop :=
  exists lower : X,
    forall x : X, s x -> q245098_le O lower x.

Definition q245098_is_lub
    {X : Type}
    (O : q245098_linear_order X)
    (s : q245098_set X)
    (upper : X) : Prop :=
  (forall x : X, s x -> q245098_le O x upper) /\
  (forall bound : X,
    (forall x : X, s x -> q245098_le O x bound) ->
    q245098_le O upper bound).

Definition q245098_is_glb
    {X : Type}
    (O : q245098_linear_order X)
    (s : q245098_set X)
    (lower : X) : Prop :=
  (forall x : X, s x -> q245098_le O lower x) /\
  (forall bound : X,
    (forall x : X, s x -> q245098_le O bound x) ->
    q245098_le O bound lower).

Record q245098_conditionally_complete
    {X : Type}
    (O : q245098_linear_order X) : Type := {
  q245098_exists_lub :
    forall s : q245098_set X,
      q245098_nonempty s ->
      q245098_bounded_above O s ->
      exists upper : X, q245098_is_lub O s upper;
  q245098_exists_glb :
    forall s : q245098_set X,
      q245098_nonempty s ->
      q245098_bounded_below O s ->
      exists lower : X, q245098_is_glb O s lower
}.

Definition q245098_densely_ordered
    {X : Type}
    (O : q245098_linear_order X) : Prop :=
  forall x y : X,
    q245098_lt O x y ->
    exists z : X,
      q245098_lt O x z /\ q245098_lt O z y.

Record q245098_topological_space (X : Type) : Type := {
  q245098_is_open : q245098_set X -> Prop;
  q245098_open_ext :
    forall U V : q245098_set X,
      (forall x : X, U x <-> V x) ->
      (q245098_is_open U <-> q245098_is_open V);
  q245098_open_univ :
    q245098_is_open (fun _ : X => True);
  q245098_open_inter :
    forall U V : q245098_set X,
      q245098_is_open U ->
      q245098_is_open V ->
      q245098_is_open (fun x : X => U x /\ V x);
  q245098_open_sUnion :
    forall family : q245098_set (q245098_set X),
      (forall U : q245098_set X,
        family U -> q245098_is_open U) ->
      q245098_is_open
        (fun x : X =>
          exists U : q245098_set X, family U /\ U x)
}.

Arguments q245098_is_open {X} _ _.

Definition q245098_neighborhood
    {X : Type}
    (T : q245098_topological_space X)
    (x : X)
    (U : q245098_set X) : Prop :=
  exists V : q245098_set X,
    q245098_is_open T V /\
    V x /\
    q245098_subset V U.

Definition q245098_generated_order_open
    {X : Type}
    (O : q245098_linear_order X)
    (U : q245098_set X) : Prop :=
  forall T : q245098_topological_space X,
    (forall a : X,
      q245098_is_open T
        (fun x : X => q245098_lt O a x)) ->
    (forall a : X,
      q245098_is_open T
        (fun x : X => q245098_lt O x a)) ->
    q245098_is_open T U.

Definition q245098_order_topology
    {X : Type}
    (O : q245098_linear_order X)
    (T : q245098_topological_space X) : Prop :=
  forall U : q245098_set X,
    q245098_is_open T U <->
    q245098_generated_order_open O U.

Definition q245098_order_closed_topology
    {X : Type}
    (O : q245098_linear_order X)
    (T : q245098_topological_space X) : Prop :=
  forall x y : X,
    ~ q245098_le O x y ->
    exists U V : q245098_set X,
      q245098_neighborhood T x U /\
      q245098_neighborhood T y V /\
      forall u v : X,
        U u -> V v -> ~ q245098_le O u v.

Definition q245098_closed_interval
    {X : Type}
    (O : q245098_linear_order X)
    (a b : X) : q245098_set X :=
  fun x : X =>
    q245098_le O a x /\ q245098_le O x b.

Definition q245098_continuous_within_at
    {X Y : Type}
    (TX : q245098_topological_space X)
    (TY : q245098_topological_space Y)
    (f : X -> Y)
    (s : q245098_set X)
    (x : X) : Prop :=
  forall V : q245098_set Y,
    q245098_neighborhood TY (f x) V ->
    exists U : q245098_set X,
      q245098_neighborhood TX x U /\
      forall y : X, s y -> U y -> V (f y).

Definition q245098_continuous_on
    {X Y : Type}
    (TX : q245098_topological_space X)
    (TY : q245098_topological_space Y)
    (f : X -> Y)
    (s : q245098_set X) : Prop :=
  forall x : X,
    s x ->
    q245098_continuous_within_at TX TY f s x.

Theorem intermediate_value_Icc :
  forall (Alpha Delta : Type)
         (OA : q245098_linear_order Alpha)
         (CCA : q245098_conditionally_complete OA)
         (DenseA : q245098_densely_ordered OA)
         (TA : q245098_topological_space Alpha)
         (OrderTA : q245098_order_topology OA TA)
         (OD : q245098_linear_order Delta)
         (TD : q245098_topological_space Delta)
         (ClosedTD : q245098_order_closed_topology OD TD)
         (a b : Alpha)
         (f : Alpha -> Delta),
    q245098_le OA a b ->
    q245098_continuous_on TA TD f
      (q245098_closed_interval OA a b) ->
    forall y : Delta,
      q245098_le OD (f a) y ->
      q245098_le OD y (f b) ->
      exists x : Alpha,
        q245098_closed_interval OA a b x /\
        f x = y.
Admitted.
