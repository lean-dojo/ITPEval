(*
  Forcing extension theorem for countable transitive models of ZF.

  Unlike a bare signature with unconstrained predicates, this statement gives
  the ambient membership relation a Tarski semantics and spells out the ZF
  axioms, the axiom of choice, omega, and ordinals relative to a class.
*)

From Stdlib Require Import Arith.PeanoNat Logic.Classical.

Set Implicit Arguments.

Section ForcingExtension.

Variable V : Type.
Variable member : V -> V -> Prop.

Definition set_class : Type := V -> Prop.

Definition full_class : set_class :=
  fun _ => True.

Definition elements (a : V) : set_class :=
  fun x => member x a.

Definition class_included (A B : set_class) : Prop :=
  forall x, A x -> B x.

Definition same_class (A B : set_class) : Prop :=
  forall x, A x <-> B x.

Definition equinumerous (A B : set_class) : Prop :=
  exists f : V -> V,
    (forall x, A x -> B (f x)) /\
    (forall x y, A x -> A y -> f x = f y -> x = y) /\
    (forall y, B y -> exists x, A x /\ f x = y).

Definition transitive_class (M : set_class) : Prop :=
  forall x y, member x y -> M y -> M x.

Definition assignment_in (M : set_class) (rho : nat -> V) : Prop :=
  forall n, M (rho n).

Definition extend_assignment (rho : nat -> V) (x : V) : nat -> V :=
  fun n =>
    match n with
    | O => x
    | S k => rho k
    end.

Inductive formula : Type :=
| FEqual : nat -> nat -> formula
| FMember : nat -> nat -> formula
| FFalse : formula
| FAnd : formula -> formula -> formula
| FOr : formula -> formula -> formula
| FImplies : formula -> formula -> formula
| FNot : formula -> formula
| FForall : formula -> formula
| FExists : formula -> formula.

Fixpoint satisfies
    (M : set_class) (rho : nat -> V) (phi : formula) : Prop :=
  match phi with
  | FEqual i j => rho i = rho j
  | FMember i j => member (rho i) (rho j)
  | FFalse => False
  | FAnd lhs rhs =>
      satisfies M rho lhs /\ satisfies M rho rhs
  | FOr lhs rhs =>
      satisfies M rho lhs \/ satisfies M rho rhs
  | FImplies lhs rhs =>
      satisfies M rho lhs -> satisfies M rho rhs
  | FNot body =>
      ~ satisfies M rho body
  | FForall body =>
      forall x, M x -> satisfies M (extend_assignment rho x) body
  | FExists body =>
      exists x, M x /\ satisfies M (extend_assignment rho x) body
  end.

Definition subset_in (M : set_class) (a b : V) : Prop :=
  forall x, M x -> member x a -> member x b.

Definition empty_in (M : set_class) (e : V) : Prop :=
  M e /\ forall x, M x -> ~ member x e.

Definition successor_in (M : set_class) (a successor : V) : Prop :=
  M successor /\
  forall x, M x ->
    (member x successor <-> member x a \/ x = a).

Definition inductive_set (M : set_class) (a : V) : Prop :=
  M a /\
  exists e,
    empty_in M e /\
    member e a /\
    forall x, M x -> member x a ->
      exists successor,
        successor_in M x successor /\
        member successor a.

Definition is_omega (M : set_class) (omega : V) : Prop :=
  inductive_set M omega /\
  forall a, inductive_set M a -> subset_in M omega a.

Definition transitive_set (M : set_class) (a : V) : Prop :=
  M a /\
  forall x y,
    M x -> M y ->
    member x y -> member y a ->
    member x a.

Definition membership_well_orders (M : set_class) (a : V) : Prop :=
  (forall x, M x -> member x a -> ~ member x x) /\
  (forall x y z,
      M x -> M y -> M z ->
      member x y -> member y z -> member z a ->
      member x z) /\
  (forall x y,
      M x -> M y ->
      member x a -> member y a ->
      x = y \/ member x y \/ member y x) /\
  (forall A : set_class,
      (exists x, A x) ->
      class_included A (elements a) ->
      exists least,
        A least /\
        forall x, A x -> x = least \/ member least x).

Definition is_ordinal (M : set_class) (a : V) : Prop :=
  transitive_set M a /\ membership_well_orders M a.

Definition models_extensionality (M : set_class) : Prop :=
  forall a b,
    M a -> M b ->
    (forall x, M x -> (member x a <-> member x b)) ->
    a = b.

Definition models_empty_set (M : set_class) : Prop :=
  exists e, empty_in M e.

Definition models_pairing (M : set_class) : Prop :=
  forall a b,
    M a -> M b ->
    exists pair,
      M pair /\
      forall x, M x ->
        (member x pair <-> x = a \/ x = b).

Definition models_union (M : set_class) : Prop :=
  forall a,
    M a ->
    exists union,
      M union /\
      forall x, M x ->
        (member x union <->
         exists y, M y /\ member x y /\ member y a).

Definition models_power_set (M : set_class) : Prop :=
  forall a,
    M a ->
    exists power,
      M power /\
      forall x, M x ->
        (member x power <-> subset_in M x a).

Definition models_infinity (M : set_class) : Prop :=
  exists infinity, inductive_set M infinity.

Definition models_separation (M : set_class) : Prop :=
  forall (phi : formula) (rho : nat -> V) (a : V),
    assignment_in M rho ->
    M a ->
    exists subset,
      M subset /\
      forall x, M x ->
        (member x subset <->
         member x a /\
         satisfies M (extend_assignment rho x) phi).

Definition replacement_holds
    (M : set_class) (rho : nat -> V) (phi : formula)
    (x y : V) : Prop :=
  satisfies M
    (extend_assignment (extend_assignment rho x) y)
    phi.

Definition models_replacement (M : set_class) : Prop :=
  forall (phi : formula) (rho : nat -> V) (a : V),
    assignment_in M rho ->
    M a ->
    (forall x,
        M x -> member x a ->
        exists! y, M y /\ replacement_holds M rho phi x y) ->
    exists image,
      M image /\
      forall y, M y ->
        (member y image <->
         exists x,
           M x /\
           member x a /\
           replacement_holds M rho phi x y).

Definition models_foundation (M : set_class) : Prop :=
  forall a,
    M a ->
    (exists x, M x /\ member x a) ->
    exists minimal,
      M minimal /\
      member minimal a /\
      forall x, M x ->
        member x minimal ->
        ~ member x a.

Record models_ZF (M : set_class) : Prop := {
  zf_extensionality : models_extensionality M;
  zf_empty_set : models_empty_set M;
  zf_pairing : models_pairing M;
  zf_union : models_union M;
  zf_power_set : models_power_set M;
  zf_infinity : models_infinity M;
  zf_separation : models_separation M;
  zf_replacement : models_replacement M;
  zf_foundation : models_foundation M
}.

Definition nonempty_in (M : set_class) (a : V) : Prop :=
  exists x, M x /\ member x a.

Definition singleton_in
    (M : set_class) (x singleton : V) : Prop :=
  M singleton /\
  forall z, M z ->
    (member z singleton <-> z = x).

Definition unordered_pair_in
    (M : set_class) (x y pair : V) : Prop :=
  M pair /\
  forall z, M z ->
    (member z pair <-> z = x \/ z = y).

Definition ordered_pair_in
    (M : set_class) (x y pair : V) : Prop :=
  exists singleton unordered,
    singleton_in M x singleton /\
    unordered_pair_in M x y unordered /\
    M pair /\
    forall z, M z ->
      (member z pair <-> z = singleton \/ z = unordered).

Definition choice_graph_for
    (M : set_class) (family graph : V) : Prop :=
  M graph /\
  forall a,
    M a -> member a family ->
    exists selected pair,
      M selected /\
      member selected a /\
      ordered_pair_in M a selected pair /\
      member pair graph /\
      forall other other_pair,
        M other ->
        ordered_pair_in M a other other_pair ->
        member other_pair graph ->
        other = selected.

Definition models_choice (M : set_class) : Prop :=
  forall family,
    M family ->
    (forall a, M a -> member a family -> nonempty_in M a) ->
    exists graph, choice_graph_for M family graph.

Definition models_ZFC (M : set_class) : Prop :=
  models_ZF M /\ models_choice M.

Theorem extensions_of_countable_transitive_models :
  forall omega,
    models_ZF full_class ->
    is_omega full_class omega ->
    forall M : set_class,
      equinumerous M (elements omega) ->
      transitive_class M ->
      models_ZF M ->
      exists N : set_class,
        class_included M N /\
        equinumerous N (elements omega) /\
        transitive_class N /\
        models_ZF N /\
        ~ same_class M N /\
        (forall alpha,
            is_ordinal full_class alpha ->
            (M alpha <-> N alpha)) /\
        (models_choice M -> models_ZFC N).
Proof.
Admitted.

End ForcingExtension.
