(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527263
  (thousand-theorems__hol-light__Q3527263), "Kleene fixed-point theorem": the
  least fixed point of an omega-Scott-
  continuous monotone self-map of a complete lattice is the supremum of its
  finite iterates from bottom. This file contains no proof.
*)

let q3527263_output = open_out "/dev/null";;
let q3527263_formatter = Format.formatter_of_out_channel q3527263_output;;
let q3527263_previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file q3527263_formatter path);;
let q3527263_library_loaded =
  Toploop.use_file q3527263_formatter "Library/iter.ml";;
Hol_loader.file_loader := q3527263_previous_file_loader;;
Format.pp_print_flush q3527263_formatter ();;
close_out q3527263_output;;
if not q3527263_library_loaded then
  failwith "failed to load Library/iter.ml";;

let Q3527263_KLEENE_FIXED_POINT_THEOREM =
  `let is_partial_order =
     \(le:A->A->bool).
       (!x:A. le x x) /\
       (!x y:A. le x y /\ le y x ==> x = y) /\
       (!x y z:A. le x y /\ le y z ==> le x z) in
   let is_supremum =
     \(le:A->A->bool) (s:A->bool) (u:A).
       (!x:A. x IN s ==> le x u) /\
       (!v:A. (!x:A. x IN s ==> le x v) ==> le u v) in
   let is_infimum =
     \(le:A->A->bool) (s:A->bool) (l:A).
       (!x:A. x IN s ==> le l x) /\
       (!v:A. (!x:A. x IN s ==> le v x) ==> le v l) in
   let is_complete_lattice =
     \(le:A->A->bool) (sSup:(A->bool)->A) (sInf:(A->bool)->A).
       is_partial_order le /\
       (!s:A->bool. is_supremum le s (sSup s)) /\
       (!s:A->bool. is_infimum le s (sInf s)) in
   let is_monotone =
     \(le:A->A->bool) (f:A->A).
       !x y:A. le x y ==> le (f x) (f y) in
   let is_omega_scott_continuous =
     \(le:A->A->bool) (sSup:(A->bool)->A) (f:A->A).
       !c:num->A.
         (!m n:num. m <= n ==> le (c m) (c n))
         ==> f (sSup (IMAGE c (:num))) =
             sSup (IMAGE (\n:num. f (c n)) (:num)) in
   let least_fixed_point =
     \(le:A->A->bool) (sInf:(A->bool)->A) (f:A->A).
       sInf {x:A | le (f x) x} in
   !le:A->A->bool.
   !sSup:(A->bool)->A.
   !sInf:(A->bool)->A.
   !f:A->A.
     is_complete_lattice le sSup sInf /\
     is_monotone le f /\
     is_omega_scott_continuous le sSup f
     ==> least_fixed_point le sInf f =
         sSup
           (IMAGE
             (\n:num. ITER n f (sSup ({}:A->bool)))
             (:num))`;;
