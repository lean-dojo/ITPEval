(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1050203 (thousand-theorems__hol4__Q1050203), "Cantor's intersection
  theorem": a nonempty downward-directed family of nonempty compact closed
  sets has nonempty total intersection. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory topologyTheory;

val IsCompact_nonempty_sInter_of_directed_nonempty_isCompact_isClosed =
  ``!(top : 'a topology) (S : ('a set) set).
      topspace top = UNIV /\
      S <> {} /\
      (!U : 'a set. U IN S ==> U <> {}) /\
      (!U : 'a set. U IN S ==> compact_in top U) /\
      (!U : 'a set. U IN S ==> closed_in top U) /\
      (!U V : 'a set.
         U IN S /\ V IN S
         ==>
         ?W : 'a set. W IN S /\ W SUBSET U /\ W SUBSET V)
      ==>
      BIGINTER S <> {}``;
