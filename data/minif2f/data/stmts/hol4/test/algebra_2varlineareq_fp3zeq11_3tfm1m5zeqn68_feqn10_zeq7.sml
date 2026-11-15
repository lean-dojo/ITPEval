(*
  Statement-only formalization of miniF2F test problem
  algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7: two complex linear equations
  determining f and z. This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7 =
  ``!f z : complex.
      (f + 3 * z = 11) /\
      (3 * (f - 1) - 5 * z = -68)
      ==>
      (f = -10) /\ (z = 7)``;
