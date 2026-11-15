(*
  Statement-only formalization of Thousand Theorems corpus artifact Q179208
  (thousand-theorems__rocq__Q179208), "Cayley's theorem": every group acting
  faithfully on an arbitrary type is multiplicatively equivalent to the range
  of its induced action in the permutation group. This file contains no proof.
*)

Set Universe Polymorphism.
Unset Implicit Arguments.

Record q179208_group (G : Type) : Type := {
  q179208_mul : G -> G -> G;
  q179208_one : G;
  q179208_inv : G -> G;
  q179208_mul_assoc :
    forall x y z : G,
      q179208_mul x (q179208_mul y z) =
      q179208_mul (q179208_mul x y) z;
  q179208_one_mul :
    forall x : G, q179208_mul q179208_one x = x;
  q179208_mul_one :
    forall x : G, q179208_mul x q179208_one = x;
  q179208_inv_mul :
    forall x : G, q179208_mul (q179208_inv x) x = q179208_one;
  q179208_mul_inv :
    forall x : G, q179208_mul x (q179208_inv x) = q179208_one
}.

Arguments q179208_mul {G} _ _ _.
Arguments q179208_one {G} _.
Arguments q179208_inv {G} _ _.

Record q179208_mul_action
    (G H : Type)
    (grp : q179208_group G) : Type := {
  q179208_act : G -> H -> H;
  q179208_one_act :
    forall x : H, q179208_act (q179208_one grp) x = x;
  q179208_mul_act :
    forall (g k : G) (x : H),
      q179208_act (q179208_mul grp g k) x =
      q179208_act g (q179208_act k x)
}.

Arguments q179208_act {G H grp} _ _ _.

Definition q179208_faithful_action
    {G H : Type}
    (grp : q179208_group G)
    (action : q179208_mul_action G H grp) : Prop :=
  forall g k : G,
    (forall x : H, q179208_act action g x = q179208_act action k x) ->
    g = k.

Record q179208_permutation (H : Type) : Type := {
  q179208_perm_apply : H -> H;
  q179208_perm_inverse : H -> H;
  q179208_perm_inverse_left :
    forall x : H,
      q179208_perm_inverse (q179208_perm_apply x) = x;
  q179208_perm_inverse_right :
    forall x : H,
      q179208_perm_apply (q179208_perm_inverse x) = x
}.

Arguments q179208_perm_apply {H} _ _.
Arguments q179208_perm_inverse {H} _ _.

Record q179208_action_range
    (G H : Type)
    (grp : q179208_group G)
    (action : q179208_mul_action G H grp) : Type := {
  q179208_range_permutation : q179208_permutation H;
  q179208_range_preimage : G;
  q179208_range_spec :
    forall x : H,
      q179208_perm_apply q179208_range_permutation x =
      q179208_act action q179208_range_preimage x
}.

Arguments q179208_range_permutation {G H grp action} _.
Arguments q179208_range_preimage {G H grp action} _.

Definition q179208_range_equal
    {G H : Type}
    {grp : q179208_group G}
    {action : q179208_mul_action G H grp}
    (p q : q179208_action_range G H grp action) : Prop :=
  forall x : H,
    q179208_perm_apply (q179208_range_permutation p) x =
    q179208_perm_apply (q179208_range_permutation q) x.

Definition q179208_range_product
    {G H : Type}
    {grp : q179208_group G}
    {action : q179208_mul_action G H grp}
    (p q r : q179208_action_range G H grp action) : Prop :=
  forall x : H,
    q179208_perm_apply (q179208_range_permutation r) x =
    q179208_perm_apply
      (q179208_range_permutation p)
      (q179208_perm_apply (q179208_range_permutation q) x).

Definition q179208_is_action_range_mul_equiv
    {G H : Type}
    (grp : q179208_group G)
    (action : q179208_mul_action G H grp) : Prop :=
  exists forward : G -> q179208_action_range G H grp action,
  exists backward : q179208_action_range G H grp action -> G,
    (forall (g : G) (x : H),
      q179208_perm_apply (q179208_range_permutation (forward g)) x =
      q179208_act action g x) /\
    (forall g k : G,
      q179208_range_product
        (forward g)
        (forward k)
        (forward (q179208_mul grp g k))) /\
    (forall p q : q179208_action_range G H grp action,
      q179208_range_equal p q ->
      backward p = backward q) /\
    (forall g : G, backward (forward g) = g) /\
    (forall p : q179208_action_range G H grp action,
      q179208_range_equal (forward (backward p)) p).

Theorem Equiv_Perm_subgroupOfMulAction :
  forall (G H : Type)
         (grp : q179208_group G)
         (action : q179208_mul_action G H grp),
    q179208_faithful_action grp action ->
    q179208_is_action_range_mul_equiv grp action.
Admitted.
