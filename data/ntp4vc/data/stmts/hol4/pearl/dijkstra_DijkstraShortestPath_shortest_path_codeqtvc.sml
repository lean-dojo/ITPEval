(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/dijkstra_DijkstraShortestPath_shortest_path_codeqtvc: Dijkstra's
  shortest-path verification condition over a finite directed graph with
  nonnegative integer edge weights. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory pred_setTheory;

val (dijkstra_path_rules,
     dijkstra_path_ind,
     dijkstra_path_cases) =
  Hol_reln `
    (!g_succ weight x.
       dijkstra_path g_succ weight x x (0 : int)) /\
    (!g_succ weight x y d z.
       dijkstra_path g_succ weight x y d /\
       z IN g_succ y ==>
       dijkstra_path g_succ weight x z (d + weight y z))
  `;

val dijkstra_min_def = Define `
  dijkstra_min to_fset lookup m q d <=>
    m IN to_fset q /\
    !x.
      x IN to_fset q ==>
      lookup d m <= lookup d x`;

val dijkstra_shortest_path_def = Define `
  dijkstra_shortest_path g_succ weight x y d <=>
    dijkstra_path g_succ weight x y d /\
    !d'.
      dijkstra_path g_succ weight x y d' ==>
      d <= d'`;

val dijkstra_inv_src_def = Define `
  dijkstra_inv_src to_fset src s q <=>
    src IN to_fset s \/ src IN to_fset q`;

val dijkstra_inv_def = Define `
  dijkstra_inv vertices to_fset g_succ weight lookup src s q d <=>
    dijkstra_inv_src to_fset src s q /\
    lookup d src = (0 : int) /\
    to_fset s SUBSET vertices /\
    to_fset q SUBSET vertices /\
    (!v1.
       v1 IN to_fset q ==>
       v1 NOTIN to_fset s) /\
    (!v1.
       v1 IN to_fset s ==>
       dijkstra_shortest_path
         g_succ weight src v1 (lookup d v1)) /\
    (!v1.
       v1 IN to_fset q ==>
       dijkstra_path
         g_succ weight src v1 (lookup d v1))`;

val dijkstra_inv_succ_def = Define `
  dijkstra_inv_succ
      to_fset g_succ weight lookup
      (x_src : 'vertex) s q d <=>
    !x.
      x IN to_fset s ==>
      !y.
        y IN g_succ x ==>
        (y IN to_fset s \/ y IN to_fset q) /\
        lookup d y <= lookup d x + weight x y`;

val dijkstra_inv_succ2_def = Define `
  dijkstra_inv_succ2
      to_fset g_succ weight lookup
      (x_src : 'vertex) s q d u su <=>
    !x.
      x IN to_fset s ==>
      !y.
        y IN g_succ x ==>
        ((x <> u \/
          (x = u /\ y NOTIN to_fset su)) ==>
          (y IN to_fset s \/ y IN to_fset q) /\
          lookup d y <= lookup d x + weight x y)`;

val dijkstra_below_min_visited_def = Define `
  dijkstra_below_min_visited
      to_fset g_succ weight lookup src visited q d <=>
    !m.
      dijkstra_min to_fset lookup m q d ==>
      !x dx.
        dijkstra_path g_succ weight src x dx ==>
        dx < lookup d m ==>
        x IN to_fset visited`;

val dijkstra_shortest_path_code_vc =
  ``!(vertices : 'vertex set)
      (g_succ : 'vertex -> 'vertex set)
      (weight : 'vertex -> 'vertex -> int)
      (to_fset : 'setrep -> 'vertex set)
      (choose1 : 'setrep -> 'vertex)
      (lookup : 'distmap -> 'vertex -> int)
      (update : 'distmap -> 'vertex -> int -> 'distmap)
      (src : 'vertex)
      (dst : 'vertex)
      (visited : 'setrep)
      (q : 'setrep)
      (d : 'distmap).
      FINITE vertices /\
      (!x. FINITE (g_succ x)) /\
      (!s. FINITE (to_fset s)) /\
      (!s.
         to_fset s <> {} ==>
         choose1 s IN to_fset s) /\
      (!x. g_succ x SUBSET vertices) /\
      (!x y. (0 : int) <= weight x y) /\
      (!m k value x.
         lookup (update m k value) x =
         if x = k then value else lookup m x) /\
      src IN vertices /\
      dst IN vertices /\
      to_fset visited = {} /\
      to_fset q = {src}
      ==>
      let d0 = update d src (0 : int)
      in
        dijkstra_inv
          vertices to_fset g_succ weight lookup
          src visited q d0 /\
        dijkstra_inv_succ
          to_fset g_succ weight lookup
          src visited q d0 /\
        dijkstra_below_min_visited
          to_fset g_succ weight lookup
          src visited q d0 /\
        !q1 d1 visited1.
          dijkstra_inv
            vertices to_fset g_succ weight lookup
            src visited1 q1 d1 /\
          dijkstra_inv_succ
            to_fset g_succ weight lookup
            src visited1 q1 d1 /\
          dijkstra_below_min_visited
            to_fset g_succ weight lookup
            src visited1 q1 d1
          ==>
          if to_fset q1 <> {} then
            to_fset q1 <> {} /\
            !q2 u.
              dijkstra_min to_fset lookup u q1 d1 /\
              to_fset q2 = to_fset q1 DELETE u
              ==>
              !visited2.
                to_fset visited2 =
                  u INSERT to_fset visited1 /\
                (if u IN to_fset visited1 then
                   CARD (to_fset visited2) =
                   CARD (to_fset visited1)
                 else
                   &(CARD (to_fset visited2)) =
                   &(CARD (to_fset visited1)) + (1 : int))
                ==>
                !su.
                  to_fset su = g_succ u
                  ==>
                  (to_fset su SUBSET g_succ u /\
                   dijkstra_inv
                     vertices to_fset g_succ weight lookup
                     src visited2 q2 d1 /\
                   dijkstra_inv_succ2
                     to_fset g_succ weight lookup
                     src visited2 q2 d1 u su) /\
                  !su1 q3 d2.
                    to_fset su1 SUBSET g_succ u /\
                    dijkstra_inv
                      vertices to_fset g_succ weight lookup
                      src visited2 q3 d2 /\
                    dijkstra_inv_succ2
                      to_fset g_succ weight lookup
                      src visited2 q3 d2 u su1
                    ==>
                    if to_fset su1 <> {} then
                      to_fset su1 <> {} /\
                      !su2.
                        let v1 = choose1 su1
                        in
                          v1 IN to_fset su1 /\
                          to_fset su2 =
                            to_fset su1 DELETE v1
                          ==>
                          !q4 d3.
                            ((v1 IN to_fset visited2 /\
                              q4 = q3 /\
                              d3 = d2) \/
                             (v1 IN to_fset q4 /\
                              lookup d3 v1 <=
                                lookup d3 u +
                                weight u v1 /\
                              q4 = q3 /\
                              d3 = d2) \/
                             (v1 IN to_fset q4 /\
                              lookup d2 u + weight u v1 <
                                lookup d2 v1 /\
                              q4 = q3 /\
                              d3 =
                                update d2 v1
                                  (lookup d2 u +
                                   weight u v1)) \/
                             (v1 NOTIN to_fset visited2 /\
                              v1 NOTIN to_fset q3 /\
                              to_fset q4 =
                                v1 INSERT to_fset q3 /\
                              d3 =
                                update d2 v1
                                  (lookup d2 u +
                                   weight u v1)))
                            ==>
                            ((0 : int) <=
                               &(CARD (to_fset su1)) /\
                             CARD (to_fset su2) <
                               CARD (to_fset su1)) /\
                            to_fset su2 SUBSET g_succ u /\
                            dijkstra_inv
                              vertices to_fset
                              g_succ weight lookup
                              src visited2 q4 d3 /\
                            dijkstra_inv_succ2
                              to_fset g_succ weight lookup
                              src visited2 q4 d3 u su2
                    else
                      ((0 : int) <=
                         &(CARD vertices) -
                         &(CARD (to_fset visited1)) /\
                       &(CARD vertices) -
                         &(CARD (to_fset visited2)) <
                       &(CARD vertices) -
                         &(CARD (to_fset visited1))) /\
                      dijkstra_inv
                        vertices to_fset g_succ weight lookup
                        src visited2 q3 d2 /\
                      dijkstra_inv_succ
                        to_fset g_succ weight lookup
                        src visited2 q3 d2 /\
                      dijkstra_below_min_visited
                        to_fset g_succ weight lookup
                        src visited2 q3 d2
          else
            (!v1.
               v1 IN to_fset visited1 ==>
               dijkstra_shortest_path
                 g_succ weight src v1 (lookup d1 v1)) /\
            (!v1.
               v1 NOTIN to_fset visited1 ==>
               !dv.
                 ~dijkstra_path
                    g_succ weight src v1 dv)``;
