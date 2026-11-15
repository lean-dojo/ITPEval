(*
  Statement-only formalization of Thousand Theorems corpus artifact Q660799
  (thousand-theorems__rocq__Q660799), "Darboux's theorem (analysis)":
  derivatives on real intervals take intermediate values, so their images of
  order-connected or convex sets remain order-connected or convex. This file
  contains no proof.
*)

From Stdlib Require Import Reals ClassicalDescription ClassicalEpsilon.

Open Scope R_scope.

Definition q660799_set : Type := R -> Prop.

Definition q660799_closed_interval
    (a b : R) : q660799_set :=
  fun x : R => a <= x /\ x <= b.

Definition q660799_open_interval
    (a b : R) : q660799_set :=
  fun x : R => a < x /\ x < b.

Definition q660799_image
    (g : R -> R) (s : q660799_set) : q660799_set :=
  fun y : R =>
    exists x : R, s x /\ g x = y.

Definition q660799_ord_connected
    (s : q660799_set) : Prop :=
  forall a : R,
    s a ->
    forall b : R,
      s b ->
      forall x : R,
        a <= x ->
        x <= b ->
        s x.

Definition q660799_convex
    (s : q660799_set) : Prop :=
  forall x y : R,
    s x ->
    s y ->
    forall alpha beta : R,
      0 <= alpha ->
      0 <= beta ->
      alpha + beta = 1 ->
      s (alpha * x + beta * y).

Definition q660799_has_deriv_within_at
    (f : R -> R) (derivative : R)
    (s : q660799_set) (x : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : R,
        s y ->
        Rabs (y - x) < delta ->
        Rabs
          (f y - f x - derivative * (y - x))
        <= epsilon * Rabs (y - x).

Definition q660799_differentiable_within_at
    (f : R -> R) (s : q660799_set) (x : R) : Prop :=
  exists derivative : R,
    q660799_has_deriv_within_at f derivative s x.

Definition q660799_differentiable_on
    (f : R -> R) (s : q660799_set) : Prop :=
  forall x : R,
    s x ->
    q660799_differentiable_within_at f s x.

Definition q660799_deriv_within
    (f : R -> R) (s : q660799_set) (x : R) : R :=
  match excluded_middle_informative
          (q660799_has_deriv_within_at f 0 s x) with
  | left _ => 0
  | right _ =>
      match excluded_middle_informative
              (exists derivative : R,
                q660799_has_deriv_within_at f derivative s x) with
      | left _ =>
          epsilon (inhabits 0)
            (fun derivative : R =>
              q660799_has_deriv_within_at f derivative s x)
      | right _ => 0
      end
  end.

Definition q660799_univ : q660799_set :=
  fun _ : R => True.

Definition q660799_has_deriv_at
    (f : R -> R) (derivative x : R) : Prop :=
  q660799_has_deriv_within_at
    f derivative q660799_univ x.

Definition q660799_differentiable_at
    (f : R -> R) (x : R) : Prop :=
  exists derivative : R,
    q660799_has_deriv_at f derivative x.

Definition q660799_deriv
    (f : R -> R) (x : R) : R :=
  q660799_deriv_within f q660799_univ x.

Theorem exists_hasDerivWithinAt_eq_of_gt_of_lt :
  forall (f f' : R -> R) (a b m : R),
    a <= b ->
    (forall x : R,
      q660799_closed_interval a b x ->
      q660799_has_deriv_within_at
        f (f' x) (q660799_closed_interval a b) x) ->
    f' a < m ->
    m < f' b ->
    exists c : R,
      q660799_open_interval a b c /\
      f' c = m.
Admitted.

Theorem exists_hasDerivWithinAt_eq_of_lt_of_gt :
  forall (f f' : R -> R) (a b m : R),
    a <= b ->
    (forall x : R,
      q660799_closed_interval a b x ->
      q660799_has_deriv_within_at
        f (f' x) (q660799_closed_interval a b) x) ->
    m < f' a ->
    f' b < m ->
    exists c : R,
      q660799_open_interval a b c /\
      f' c = m.
Admitted.

Theorem Set_OrdConnected_image_hasDerivWithinAt :
  forall (f f' : R -> R) (s : q660799_set),
    q660799_ord_connected s ->
    (forall x : R,
      s x ->
      q660799_has_deriv_within_at f (f' x) s x) ->
    q660799_ord_connected (q660799_image f' s).
Admitted.

Theorem Set_OrdConnected_image_derivWithin :
  forall (f : R -> R) (s : q660799_set),
    q660799_ord_connected s ->
    q660799_differentiable_on f s ->
    q660799_ord_connected
      (q660799_image (q660799_deriv_within f s) s).
Admitted.

Theorem Set_OrdConnected_image_deriv :
  forall (f : R -> R) (s : q660799_set),
    q660799_ord_connected s ->
    (forall x : R,
      s x ->
      q660799_differentiable_at f x) ->
    q660799_ord_connected
      (q660799_image (q660799_deriv f) s).
Admitted.

Theorem Convex_image_hasDerivWithinAt :
  forall (f f' : R -> R) (s : q660799_set),
    q660799_convex s ->
    (forall x : R,
      s x ->
      q660799_has_deriv_within_at f (f' x) s x) ->
    q660799_convex (q660799_image f' s).
Admitted.

Theorem Convex_image_derivWithin :
  forall (f : R -> R) (s : q660799_set),
    q660799_convex s ->
    q660799_differentiable_on f s ->
    q660799_convex
      (q660799_image (q660799_deriv_within f s) s).
Admitted.

Theorem Convex_image_deriv :
  forall (f : R -> R) (s : q660799_set),
    q660799_convex s ->
    (forall x : R,
      s x ->
      q660799_differentiable_at f x) ->
    q660799_convex
      (q660799_image (q660799_deriv f) s).
Admitted.

Theorem exists_hasDerivWithinAt_eq_of_ge_of_le :
  forall (f f' : R -> R) (a b m : R),
    a <= b ->
    (forall x : R,
      q660799_closed_interval a b x ->
      q660799_has_deriv_within_at
        f (f' x) (q660799_closed_interval a b) x) ->
    f' a <= m ->
    m <= f' b ->
    exists c : R,
      q660799_closed_interval a b c /\
      f' c = m.
Admitted.

Theorem exists_hasDerivWithinAt_eq_of_le_of_ge :
  forall (f f' : R -> R) (a b m : R),
    a <= b ->
    (forall x : R,
      q660799_closed_interval a b x ->
      q660799_has_deriv_within_at
        f (f' x) (q660799_closed_interval a b) x) ->
    f' a <= m ->
    m <= f' b ->
    exists c : R,
      q660799_closed_interval a b c /\
      f' c = m.
Admitted.
