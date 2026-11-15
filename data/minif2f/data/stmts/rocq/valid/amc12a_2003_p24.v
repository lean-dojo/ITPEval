Require Import Coq.Reals.Reals.
Open Scope R_scope.



(* Zero is attained and is an upper bound, matching the IsGreatest
   formulation of the benchmark. *)
Theorem amc12a_2003_p24 :
  (exists a b : R,
    1 < b /\
    b <= a /\
    ln (a / b) / ln a + ln (b / a) / ln b = 0) /\
  forall a b : R,
    1 < b ->
    b <= a ->
    ln (a / b) / ln a + ln (b / a) / ln b <= 0.

Proof.
