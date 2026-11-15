(*
  Statement-only formalization of Thousand Theorems corpus artifact Q510197,
  "Tutte theorem": a simple graph on an arbitrary finite vertex carrier has a
  perfect matching if and only if deleting any vertex subset leaves at most
  that many odd connected components. This file contains no proof.
*)

needs "Library/rstc.ml";;

let Q510197_TUTTE_THEOREM =
  `let simple_graph_on =
     \(vertices:A->bool) (g:A->A->bool).
       (!x:A. ~(g x x)) /\
       (!x y:A. g x y <=> g y x) /\
       (!x y:A. g x y ==> x IN vertices /\ y IN vertices) in
   let perfect_matching_on =
     \(vertices:A->bool) (g:A->A->bool) (m:A->A->bool).
       (!x y:A. m x y ==> x IN vertices /\ y IN vertices /\ g x y) /\
       (!x y:A. m x y <=> m y x) /\
       (!x:A. x IN vertices ==> ?!y:A. m x y) in
   let component_after_deleting =
     \(vertices:A->bool) (g:A->A->bool) (u:A->bool) (x:A).
       {y:A |
          y IN vertices /\
          ~(y IN u) /\
          RTC
            (\a b:A.
               a IN vertices /\ b IN vertices /\
               ~(a IN u) /\ ~(b IN u) /\ g a b)
            x y} in
   let odd_components_after_deleting =
     \(vertices:A->bool) (g:A->A->bool) (u:A->bool).
       {c:A->bool |
          (?x:A.
             x IN vertices /\
             ~(x IN u) /\
             c = component_after_deleting vertices g u x) /\
          ODD (CARD c)} in
   !vertices:A->bool.
   !g:A->A->bool.
     FINITE vertices /\
     simple_graph_on vertices g
     ==>
     ((?m:A->A->bool. perfect_matching_on vertices g m) <=>
      (!u:A->bool.
         u SUBSET vertices
         ==> CARD (odd_components_after_deleting vertices g u) <= CARD u))`;;
