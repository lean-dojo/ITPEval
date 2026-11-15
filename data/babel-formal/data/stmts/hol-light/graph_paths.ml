let path_RULES,path_INDUCT,path_CASES = new_inductive_definition
  `(!E:A->A->bool v. path E v v) /\
   (!E:A->A->bool u v w. path E u v /\ E v w ==> path E u w)`;;

let undirected = new_definition
  `undirected (E:A->A->bool) <=> !x y. E x y ==> E y x`;;

let erev = new_definition
  `erev (E:A->A->bool) x y <=> E y x`;;

let path_refl =
  `!E:A->A->bool v. path E v v`;;

let path_append_right =
  `!E:A->A->bool v w. path E v w ==> !u. path E u v ==> path E u w`;;

let path_trans =
  `!E:A->A->bool u v w. path E u v ==> path E v w ==> path E u w`;;

let trans = path_trans;;

let edge_path =
  `!E:A->A->bool u v. E u v ==> path E u v`;;

let concat_edge_right =
  `!E:A->A->bool u v w. path E u v ==> E v w ==> path E u w`;;

let concat = path_trans;;

let concat_edge_left =
  `!E:A->A->bool u v w. E u v ==> path E v w ==> path E u w`;;

let concat3 =
  `!E:A->A->bool u v w t.
      path E u v ==> path E v w ==> path E w t ==> path E u t`;;

let reverse_edge_Erev =
  `!E:A->A->bool v w. E v w ==> path (erev E) w v`;;

let reverse_step_Erev =
  `!E:A->A->bool u v w.
      path (erev E) v u ==> E v w ==> path (erev E) w u`;;

let reverse_in_Erev =
  `!E:A->A->bool u v. path E u v ==> path (erev E) v u`;;

let path_mono =
  `!(E:A->A->bool) (G:A->A->bool) u v.
      (!x y. E x y ==> G x y) ==> path E u v ==> path G u v`;;

let reverse_path =
  `!E:A->A->bool u v. undirected E ==> path E u v ==> path E v u`;;

let cycle_refl =
  `!E:A->A->bool v w. path E v w ==> path E w v ==> path E v v`;;
