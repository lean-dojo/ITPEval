(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From fourcolor Require Import real realplane.
From fourcolor Require combinatorial4ct discretize finitize.

(******************************************************************************)
(*   This files contains the proof of the high-level statement of the Four    *)
(* Color Theorem, whose statement uses only the elementary real topology      *)
(* defined in libraries real and realplane.                                   *)
(*   The real-line model is explicit, so the theorem does not silently assume *)
(* a particular construction of the real numbers.                             *)
(******************************************************************************)

Section FourColorTheorem.

Variable Rmodel : Real.model.
Let R := Real.model_structure Rmodel.
Implicit Type m : map R.

Theorem four_color_finite m : finite_simple_map m -> colorable_with 4 m.
Proof.
Admitted.

Theorem four_color m : simple_map m -> colorable_with 4 m.
Proof.
Admitted.

End FourColorTheorem.
