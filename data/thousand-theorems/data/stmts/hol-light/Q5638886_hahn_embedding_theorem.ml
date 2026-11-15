(*
  Statement-only formalization of Thousand Theorems corpus artifact Q5638886,
  "Hahn embedding theorem": every linearly ordered abelian group embeds
  injectively and order-additively into real Hahn series indexed by its finite
  Archimedean classes, with leading class preserved. This file contains no proof.
*)

let q5638886_output = open_out "/dev/null";;
let q5638886_formatter = Format.formatter_of_out_channel q5638886_output;;
let q5638886_previous_file_loader = !Hol_loader.file_loader;;
let q5638886_previous_verbose = !verbose;;
let q5638886_previous_type_invention_warning = !type_invention_warning;;
verbose := false;;
type_invention_warning := false;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q5638886_formatter path);;
let q5638886_library_loaded =
  Toploop.use_file q5638886_formatter "Library/grouptheory.ml";;
Hol_loader.file_loader := q5638886_previous_file_loader;;
verbose := q5638886_previous_verbose;;
type_invention_warning := q5638886_previous_type_invention_warning;;
Format.pp_print_flush q5638886_formatter ();;
close_out q5638886_output;;
if not q5638886_library_loaded then
  failwith "failed to load Library/grouptheory.ml";;

let Q5638886_HAHN_EMBEDDING_THEOREM =
  `let group_abs =
     \(G:A group) (le:A->A->bool) (x:A).
       if le (group_id G) x then x else group_neg G x in
   let is_linearly_ordered_abelian_group =
     \(G:A group) (le:A->A->bool).
       group_carrier G = (:A) /\
       abelian_group G /\
       (!x:A. le x x) /\
       (!x y z:A. le x y /\ le y z ==> le x z) /\
       (!x y:A. le x y /\ le y x ==> x = y) /\
       (!x y:A. le x y \/ le y x) /\
       (!x y z:A.
          le x y
          ==> le (group_add G z x) (group_add G z y)) in
   let archimedean_le =
     \(G:A group) (le:A->A->bool) (x:A) (y:A).
       ?n:num.
         le (group_abs G le y)
            (group_nmul G n (group_abs G le x)) in
   let archimedean_equiv =
     \(G:A group) (le:A->A->bool) (x:A) (y:A).
       archimedean_le G le x y /\
       archimedean_le G le y x in
   let archimedean_class =
     \(G:A group) (le:A->A->bool) (x:A).
       {y:A | archimedean_equiv G le x y} in
   let finite_archimedean_class =
     \(G:A group) (le:A->A->bool) (C:A->bool).
       ?x:A.
         ~(x = group_id G) /\
         C = archimedean_class G le x in
   let class_le =
     \(G:A group) (le:A->A->bool)
      (C:A->bool) (D:A->bool).
       ?x y:A.
         ~(x = group_id G) /\
         ~(y = group_id G) /\
         C = archimedean_class G le x /\
         D = archimedean_class G le y /\
         archimedean_le G le x y in
   let class_lt =
     \(G:A group) (le:A->A->bool)
      (C:A->bool) (D:A->bool).
       class_le G le C D /\ ~(class_le G le D C) in
   let hahn_support =
     \(G:A group) (le:A->A->bool)
      (s:(A->bool)->real).
       {C:A->bool |
          finite_archimedean_class G le C /\ ~(s C = &0)} in
   let well_ordered_support =
     \(G:A group) (le:A->A->bool)
      (s:(A->bool)->real).
       !U:(A->bool)->bool.
         U SUBSET hahn_support G le s /\ ~(U = {})
         ==> ?C:A->bool.
               C IN U /\
               !D:A->bool. D IN U ==> class_le G le C D in
   let is_hahn_series =
     \(G:A group) (le:A->A->bool)
      (s:(A->bool)->real).
       (!C:A->bool.
          ~(finite_archimedean_class G le C)
          ==> s C = &0) /\
       well_ordered_support G le s in
   let hahn_lt =
     \(G:A group) (le:A->A->bool)
      (s:(A->bool)->real) (t:(A->bool)->real).
       ?C:A->bool.
         finite_archimedean_class G le C /\
         (!D:A->bool.
            finite_archimedean_class G le D /\
            class_lt G le D C
            ==> s D = t D) /\
         s C < t C in
   let hahn_le =
     \(G:A group) (le:A->A->bool)
      (s:(A->bool)->real) (t:(A->bool)->real).
       s = t \/ hahn_lt G le s t in
   let leading_class_agrees =
     \(G:A group) (le:A->A->bool)
      (s:(A->bool)->real) (a:A).
       if a = group_id G then
         !C:A->bool. s C = &0
       else
         let C = archimedean_class G le a in
         finite_archimedean_class G le C /\
         ~(s C = &0) /\
         !D:A->bool.
           finite_archimedean_class G le D /\
           class_lt G le D C
           ==> s D = &0 in
   !G:A group. !le:A->A->bool.
     is_linearly_ordered_abelian_group G le
     ==> ?f:A->(A->bool)->real.
           (!x:A. is_hahn_series G le (f x)) /\
           (!C:A->bool. f (group_id G) C = &0) /\
           (!x y:A. !C:A->bool.
              f (group_add G x y) C = f x C + f y C) /\
           (!x y:A.
              le x y ==> hahn_le G le (f x) (f y)) /\
           (!x y:A. f x = f y ==> x = y) /\
           (!a:A. leading_class_agrees G le (f a) a)`;;
