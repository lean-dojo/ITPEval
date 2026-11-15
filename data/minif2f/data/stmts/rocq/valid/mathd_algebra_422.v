Require Import Reals.
Open Scope R_scope.

Theorem mathd_algebra_422 :
  forall (x : R) (sigma sigma_inv : R -> R),
    (forall y, sigma y = 5 * y - 12) ->
    (forall y, sigma_inv y = (y + 12) / 5) ->
    (* The inverse is supplied universally, so the assumptions cannot
       be discharged by choosing a function with a false specification. *)
    sigma (x + 1) = sigma_inv x ->
    x = 47 / 24.
Proof.
Admitted.
