(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_bfs_BFS_bfsqtvc: the breadth-first search verification
  condition establishing its initial frontier invariant and preserving the
  shortest-path, closure, and termination branches of the main loop. This
  file contains no proof.
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

val vstte12_bfs_BFS_bfsqtvc =
  ``!(succ : 'vertex -> 'vertex set)
      (graph_eq : 'vertex -> 'vertex -> bool)
      (to_fset : 'setrep -> 'vertex set)
      (choose1 : 'setrep -> 'vertex).
      (!x. FINITE (succ x)) /\
      (!q. FINITE (to_fset q)) /\
      (!x y. (graph_eq x y <=> x = y)) /\
      (!q.
         to_fset q <> {} ==>
         choose1 q IN to_fset q)
      ==>
      !visited o1 o2 visited1 : 'setrep.
      !s : 'vertex.
      !current : 'setrep.
      !t : 'vertex.
        to_fset visited = {} ==>
        &(CARD (to_fset visited)) = (0 : int) ==>
        to_fset o1 = {} ==>
        &(CARD (to_fset o1)) = (0 : int) ==>
        to_fset o2 = {} ==>
        &(CARD (to_fset o2)) = (0 : int) ==>
        to_fset visited1 = s INSERT to_fset visited ==>
        (if s IN to_fset visited then
           CARD (to_fset visited1) = CARD (to_fset visited)
         else
           &(CARD (to_fset visited1)) =
           &(CARD (to_fset visited)) + (1 : int)) ==>
        to_fset current = s INSERT to_fset o1 ==>
        (if s IN to_fset o1 then
           CARD (to_fset current) = CARD (to_fset o1)
         else
           &(CARD (to_fset current)) =
           &(CARD (to_fset o1)) + (1 : int)) ==>
        vstte12_bfs_inv
          succ s t
          (to_fset visited1) (to_fset current) (to_fset o2)
          (0 : int) /\
        (to_fset current = {} ==> to_fset o2 = {}) /\
        (!x.
           vstte12_bfs_closure
             succ
             (to_fset visited1) (to_fset current) (to_fset o2)
             x) /\
        (0 : int) <= (0 : int) /\
        !d : int.
        !next current1 visited2 : 'setrep.
          vstte12_bfs_inv
            succ s t
            (to_fset visited2) (to_fset current1) (to_fset next)
            d /\
          (to_fset current1 = {} ==> to_fset next = {}) /\
          (!x.
             vstte12_bfs_closure
               succ
               (to_fset visited2) (to_fset current1) (to_fset next)
               x) /\
          (0 : int) <= d
          ==>
          if to_fset current1 <> {} then
            to_fset current1 <> {} /\
            !current2 : 'setrep.
              let v = choose1 current1
              in
                v IN to_fset current1 /\
                to_fset current2 =
                  to_fset current1 DELETE v
                ==>
                (graph_eq v t <=> v = t) ==>
                if graph_eq v t then
                  vstte12_bfs_shortest_path succ s t d
                else
                  (vstte12_bfs_inv
                     succ s t
                     (to_fset visited2)
                     (to_fset current2)
                     (to_fset next)
                     d /\
                   vstte12_bfs_shortest_path succ s v d /\
                   (!x.
                      x <> v ==>
                      vstte12_bfs_closure
                        succ
                        (to_fset visited2)
                        (to_fset current2)
                        (to_fset next)
                        x)) /\
                  !next1 visited3 : 'setrep.
                    vstte12_bfs_inv
                      succ s t
                      (to_fset visited3)
                      (to_fset current2)
                      (to_fset next1)
                      d /\
                    succ v SUBSET to_fset visited3 /\
                    (!x.
                       vstte12_bfs_closure
                         succ
                         (to_fset visited3)
                         (to_fset current2)
                         (to_fset next1)
                         x)
                    ==>
                    if to_fset current2 = {} then
                      !o3 : 'setrep.
                        to_fset o3 = {} /\
                        &(CARD (to_fset o3)) = (0 : int)
                        ==>
                        vstte12_bfs_inv
                          succ s t
                          (to_fset visited3)
                          (to_fset next1)
                          (to_fset o3)
                          (d + (1 : int)) /\
                        (to_fset next1 = {} ==>
                         to_fset o3 = {}) /\
                        (!x.
                           vstte12_bfs_closure
                             succ
                             (to_fset visited3)
                             (to_fset next1)
                             (to_fset o3)
                             x) /\
                        (0 : int) <= d + (1 : int)
                    else
                      vstte12_bfs_inv
                        succ s t
                        (to_fset visited3)
                        (to_fset current2)
                        (to_fset next1)
                        d /\
                      (to_fset current2 = {} ==>
                       to_fset next1 = {}) /\
                      (!x.
                         vstte12_bfs_closure
                           succ
                           (to_fset visited3)
                           (to_fset current2)
                           (to_fset next1)
                           x) /\
                      (0 : int) <= d
          else
            !d1 : int.
              ~vstte12_bfs_path succ s t d1``;
