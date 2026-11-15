(*
  Statement-only formalization of Thousand Theorems corpus artifact Q4116459
  (thousand-theorems__rocq__Q4116459), "Niven's theorem": a rational cosine
  at a rational multiple of pi is one of -1, -1/2, 0, 1/2, or 1. This file
  contains no proof.
*)

From Stdlib Require Import Reals QArith.

Local Open Scope R_scope.

Theorem niven :
  forall theta : R,
    (exists r : Q, theta = Q2R r * PI) ->
    (exists q : Q, cos theta = Q2R q) ->
    cos theta = -1 \/
    cos theta = - (1 / 2) \/
    cos theta = 0 \/
    cos theta = 1 / 2 \/
    cos theta = 1.
Admitted.
