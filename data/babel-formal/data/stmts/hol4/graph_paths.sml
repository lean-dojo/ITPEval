(*
  Statement-only formalization of the Babel-formal topic graph_paths. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;

val (path_rules, path_ind, path_cases) = Hol_reln `
  (!E v. path (E : 'a -> 'a -> bool) v v) /\
  (!E u v w.
      path (E : 'a -> 'a -> bool) u v /\ E v w ==>
      path E u w)
`;

val undirected_def = new_definition (
  "undirected_def",
  ``undirected (E : 'a -> 'a -> bool) <=>
      !x y. E x y ==> E y x``);

val erev_def = new_definition (
  "erev_def",
  ``erev (E : 'a -> 'a -> bool) x y <=> E y x``);

val path_refl =
  ``!(E : 'a -> 'a -> bool) v. path E v v``;

val path_append_right =
  ``!(E : 'a -> 'a -> bool) v w.
      path E v w ==> !u. path E u v ==> path E u w``;

val path_trans =
  ``!(E : 'a -> 'a -> bool) u v w.
      path E u v ==> path E v w ==> path E u w``;

val trans = path_trans;

val reverse_path =
  ``!(E : 'a -> 'a -> bool) u v.
      undirected E ==> path E u v ==> path E v u``;

val concat_edge_right =
  ``!(E : 'a -> 'a -> bool) u v w.
      path E u v ==> E v w ==> path E u w``;

val concat =
  ``!(E : 'a -> 'a -> bool) u v w.
      path E u v ==> path E v w ==> path E u w``;

val edge_path =
  ``!(E : 'a -> 'a -> bool) u v.
      E u v ==> path E u v``;

val concat_edge_left =
  ``!(E : 'a -> 'a -> bool) u v w.
      E u v ==> path E v w ==> path E u w``;

val concat3 =
  ``!(E : 'a -> 'a -> bool) u v w t.
      path E u v ==> path E v w ==> path E w t ==> path E u t``;

val reverse_in_erev =
  ``!(E : 'a -> 'a -> bool) u v.
      path E u v ==> path (erev E) v u``;

val cycle_refl =
  ``!(E : 'a -> 'a -> bool) v w.
      path E v w ==> path E w v ==> path E v v``;
