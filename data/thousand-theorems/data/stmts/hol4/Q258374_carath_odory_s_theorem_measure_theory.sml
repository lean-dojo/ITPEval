(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q258374 (thousand-theorems__hol4__Q258374), "Carathéodory's theorem
  (measure theory)": the Carathéodory measurable space of an arbitrary outer
  measure consists exactly of the sets satisfying the outer-measure splitting
  criterion. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory extrealTheory sigma_algebraTheory measureTheory;

val q258374_caratheodory_def = new_definition (
  "q258374_caratheodory_def",
  ``q258374_caratheodory (m : 'a set -> extreal) =
      ((UNIV : 'a set),
       {s : 'a set |
         !t : 'a set.
           m t = m (t INTER s) + m (t DIFF s)})``);

val caratheodory_measurable_space =
  ``!(m : 'a set -> extreal).
      outer_measure_space (UNIV, POW UNIV, m)
      ==>
      sigma_algebra (q258374_caratheodory m) /\
      !s : 'a set.
        (s IN subsets (q258374_caratheodory m) <=>
         !t : 'a set.
           m t = m (t INTER s) + m (t DIFF s))``;
