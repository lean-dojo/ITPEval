(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1457052,
  "Well-ordering theorem": every type admits a strict total order that is
  well-founded. This file contains no proof.
*)

let Q1457052_WELL_ORDERING_THEOREM =
  `?lt:A->A->bool.
      (!x:A. ~(lt x x)) /\
      (!x y z:A. lt x y /\ lt y z ==> lt x z) /\
      (!x y:A. lt x y \/ x = y \/ lt y x) /\
      WF lt`;;
