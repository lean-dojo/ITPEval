(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_bfs_BFS_fill_nextqtvc: the breadth-first-search fill-next
  verification condition for processing a vertex's successors while
  preserving the frontier invariant, visited-set closure, and loop progress.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory pred_setTheory;

val vstte12_bfs_path_def = Define `
  vstte12_bfs_path
      (succ : 'vertex -> 'vertex set)
      (v1 : 'vertex) (v2 : 'vertex) (n : int) <=>
    ?k : num.
      n = &k /\
      ?walk : num -> 'vertex.
        walk 0 = v1 /\
        walk k = v2 /\
        !i. i < k ==> walk (SUC i) IN succ (walk i)`;

val vstte12_bfs_shortest_path_def = Define `
  vstte12_bfs_shortest_path succ v1 v2 n <=>
    vstte12_bfs_path succ v1 v2 n /\
    !m : int.
      m < n ==>
      ~vstte12_bfs_path succ v1 v2 m`;

val vstte12_bfs_inv_def = Define `
  vstte12_bfs_inv succ s t visited current next d <=>
    current SUBSET visited /\
    (!x.
       x IN current ==>
       vstte12_bfs_shortest_path succ s x d) /\
    next SUBSET visited /\
    (!x.
       x IN next ==>
       vstte12_bfs_shortest_path succ s x (d + (1 : int))) /\
    (!x m.
       vstte12_bfs_path succ s x m ==>
       m <= d ==>
       x IN visited) /\
    (!x.
       x IN visited ==>
       ?m : int.
         vstte12_bfs_path succ s x m /\
         m <= d + (1 : int)) /\
    (!x.
       vstte12_bfs_shortest_path succ s x (d + (1 : int)) ==>
       x IN next \/ ~(x IN visited)) /\
    (t IN visited ==> t IN current \/ t IN next)`;

val vstte12_bfs_closure_def = Define `
  vstte12_bfs_closure succ visited current next x <=>
    x IN visited ==>
    ~(x IN current) ==>
    ~(x IN next) ==>
    !y. y IN succ x ==> y IN visited`;

val vstte12_bfs_BFS_fill_nextqtvc =
  ``!(succ : 'vertex -> 'vertex set)
      (to_fset : 'setrep -> 'vertex set)
      (choose1 : 'setrep -> 'vertex).
      (!x. FINITE (succ x)) /\
      (!q. FINITE (to_fset q)) /\
      (!q.
         to_fset q <> {} ==>
         choose1 q IN to_fset q)
      ==>
      !s t : 'vertex.
      !visited current next acc : 'setrep.
      !d : int.
      !v : 'vertex.
        vstte12_bfs_inv
          succ s t
          (to_fset visited) (to_fset current) (to_fset next)
          d ==>
        vstte12_bfs_shortest_path succ s v d ==>
        (!x.
           x <> v ==>
           vstte12_bfs_closure
             succ
             (to_fset visited) (to_fset current) (to_fset next)
             x) ==>
        to_fset acc = succ v ==>
        vstte12_bfs_inv
          succ s t
          (to_fset visited) (to_fset current) (to_fset next)
          d /\
        to_fset acc SUBSET succ v /\
        succ v DIFF to_fset acc SUBSET to_fset visited /\
        (!x.
           x <> v ==>
           vstte12_bfs_closure
             succ
             (to_fset visited) (to_fset current) (to_fset next)
             x) /\
        !acc1 next1 visited1 : 'setrep.
          vstte12_bfs_inv
            succ s t
            (to_fset visited1) (to_fset current) (to_fset next1)
            d /\
          to_fset acc1 SUBSET succ v /\
          succ v DIFF to_fset acc1 SUBSET to_fset visited1 /\
          (!x.
             x <> v ==>
             vstte12_bfs_closure
               succ
               (to_fset visited1) (to_fset current) (to_fset next1)
               x)
          ==>
          if to_fset acc1 <> {} then
            to_fset acc1 <> {} /\
            !acc2 : 'setrep.
              let w = choose1 acc1
              in
                w IN to_fset acc1 /\
                to_fset acc2 = to_fset acc1 DELETE w
                ==>
                if ~(w IN to_fset visited1) then
                  !visited2 : 'setrep.
                    to_fset visited2 =
                      w INSERT to_fset visited1 /\
                    (if w IN to_fset visited1 then
                       CARD (to_fset visited2) =
                       CARD (to_fset visited1)
                     else
                       &(CARD (to_fset visited2)) =
                       &(CARD (to_fset visited1)) + (1 : int))
                    ==>
                    !next2 : 'setrep.
                      to_fset next2 =
                        w INSERT to_fset next1 /\
                      (if w IN to_fset next1 then
                         CARD (to_fset next2) =
                         CARD (to_fset next1)
                       else
                         &(CARD (to_fset next2)) =
                         &(CARD (to_fset next1)) + (1 : int))
                      ==>
                      ((0 : int) <= &(CARD (to_fset acc1)) /\
                       CARD (to_fset acc2) <
                       CARD (to_fset acc1)) /\
                      vstte12_bfs_inv
                        succ s t
                        (to_fset visited2)
                        (to_fset current)
                        (to_fset next2)
                        d /\
                      to_fset acc2 SUBSET succ v /\
                      succ v DIFF to_fset acc2
                        SUBSET to_fset visited2 /\
                      (!x.
                         x <> v ==>
                         vstte12_bfs_closure
                           succ
                           (to_fset visited2)
                           (to_fset current)
                           (to_fset next2)
                           x)
                else
                  ((0 : int) <= &(CARD (to_fset acc1)) /\
                   CARD (to_fset acc2) <
                   CARD (to_fset acc1)) /\
                  vstte12_bfs_inv
                    succ s t
                    (to_fset visited1)
                    (to_fset current)
                    (to_fset next1)
                    d /\
                  to_fset acc2 SUBSET succ v /\
                  succ v DIFF to_fset acc2
                    SUBSET to_fset visited1 /\
                  (!x.
                     x <> v ==>
                     vstte12_bfs_closure
                       succ
                       (to_fset visited1)
                       (to_fset current)
                       (to_fset next1)
                       x)
          else
            vstte12_bfs_inv
              succ s t
              (to_fset visited1) (to_fset current) (to_fset next1)
              d /\
            succ v SUBSET to_fset visited1 /\
            (!x.
               vstte12_bfs_closure
                 succ
                 (to_fset visited1) (to_fset current) (to_fset next1)
                 x)``;
