(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_bfs_BFS_bfsqtvc: the breadth-first-search verification
  condition for shortest paths, preserving the visited/current/next frontier
  invariant, successor closure, loop progress, and the found-or-unreachable
  result. This file contains no proof.
*)

ignore
  (new_inductive_definition
   `(!succ:A->A->bool.
     !v:A.
       ntp4vc_vstte12_bfs_path succ v v (&0:int)) /\
    (!succ:A->A->bool.
     !v1 v2 v3:A.
     !n:int.
       ntp4vc_vstte12_bfs_path succ v1 v2 n /\
       v3 IN succ v2
       ==> ntp4vc_vstte12_bfs_path succ v1 v3 (n + (&1:int)))`);;

ignore
  (new_definition
  `ntp4vc_vstte12_bfs_shortest_path
    (succ:A->A->bool) (v1:A) (v2:A) (n:int) <=>
    ntp4vc_vstte12_bfs_path succ v1 v2 n /\
    (!m:int.
       m < n
       ==> ~ntp4vc_vstte12_bfs_path succ v1 v2 m)`);;

ignore
  (new_definition
  `ntp4vc_vstte12_bfs_inv
    (succ:A->A->bool)
    (s:A)
    (t:A)
    (visited:A->bool)
    (current:A->bool)
    (next:A->bool)
    (d:int) <=>
    current SUBSET visited /\
    (!x:A.
       x IN current
       ==> ntp4vc_vstte12_bfs_shortest_path succ s x d) /\
    next SUBSET visited /\
    (!x:A.
       x IN next
       ==> ntp4vc_vstte12_bfs_shortest_path
             succ s x (d + (&1:int))) /\
    (!x:A.
     !m:int.
       ntp4vc_vstte12_bfs_path succ s x m
       ==> m <= d
       ==> x IN visited) /\
    (!x:A.
       x IN visited
       ==> ?m:int.
             ntp4vc_vstte12_bfs_path succ s x m /\
             m <= d + (&1:int)) /\
    (!x:A.
       ntp4vc_vstte12_bfs_shortest_path
         succ s x (d + (&1:int))
       ==> x IN next \/ ~(x IN visited)) /\
    (t IN visited ==> t IN current \/ t IN next)`);;

ignore
  (new_definition
  `ntp4vc_vstte12_bfs_closure
    (succ:A->A->bool)
    (visited:A->bool)
    (current:A->bool)
    (next:A->bool)
    (x:A) <=>
    x IN visited
    ==> ~(x IN current)
    ==> ~(x IN next)
    ==> !y:A. y IN succ x ==> y IN visited`);;

ignore
 `!succ:A->A->bool.
  !to_fset:S->A->bool.
  !choose:S->A.
  !eq:A->A->bool.
  !visited o1 o2 visited1:S.
  !s:A.
  !current:S.
  !t:A.
    (!x:A. FINITE (succ x)) /\
    (!q:S. FINITE (to_fset q))
    ==>
    to_fset visited = ({}:A->bool)
    ==>
    (&(CARD (to_fset visited)):int) = (&0:int)
    ==>
    to_fset o1 = ({}:A->bool)
    ==>
    (&(CARD (to_fset o1)):int) = (&0:int)
    ==>
    to_fset o2 = ({}:A->bool)
    ==>
    (&(CARD (to_fset o2)):int) = (&0:int)
    ==>
    to_fset visited1 = s INSERT to_fset visited
    ==>
    (if s IN to_fset visited then
       CARD (to_fset visited1) = CARD (to_fset visited)
     else
       (&(CARD (to_fset visited1)):int) =
       (&(CARD (to_fset visited)):int) + (&1:int))
    ==>
    to_fset current = s INSERT to_fset o1
    ==>
    (if s IN to_fset o1 then
       CARD (to_fset current) = CARD (to_fset o1)
     else
       (&(CARD (to_fset current)):int) =
       (&(CARD (to_fset o1)):int) + (&1:int))
    ==>
    ntp4vc_vstte12_bfs_inv
      succ s t
      (to_fset visited1) (to_fset current) (to_fset o2) (&0:int) /\
    (to_fset current = ({}:A->bool)
     ==> to_fset o2 = ({}:A->bool)) /\
    (!x:A.
       ntp4vc_vstte12_bfs_closure
         succ (to_fset visited1) (to_fset current) (to_fset o2) x) /\
    (&0:int) <= (&0:int) /\
    (!d:int.
     !next current1 visited2:S.
       ntp4vc_vstte12_bfs_inv
         succ s t
         (to_fset visited2) (to_fset current1) (to_fset next) d /\
       (to_fset current1 = ({}:A->bool)
        ==> to_fset next = ({}:A->bool)) /\
       (!x:A.
          ntp4vc_vstte12_bfs_closure
            succ
            (to_fset visited2) (to_fset current1) (to_fset next) x) /\
       (&0:int) <= d
       ==>
       if ~(to_fset current1 = ({}:A->bool)) then
         ~(to_fset current1 = ({}:A->bool)) /\
         (!current2:S.
            let v = choose current1 in
            v IN to_fset current1 /\
            to_fset current2 = to_fset current1 DELETE v
            ==>
            (eq v t <=> v = t)
            ==>
            if eq v t then
              ntp4vc_vstte12_bfs_shortest_path succ s t d
            else
              (ntp4vc_vstte12_bfs_inv
                 succ s t
                 (to_fset visited2) (to_fset current2)
                 (to_fset next) d /\
               ntp4vc_vstte12_bfs_shortest_path succ s v d /\
               (!x:A.
                  ~(x = v)
                  ==> ntp4vc_vstte12_bfs_closure
                        succ
                        (to_fset visited2) (to_fset current2)
                        (to_fset next) x)) /\
              (!next1 visited3:S.
                 ntp4vc_vstte12_bfs_inv
                   succ s t
                   (to_fset visited3) (to_fset current2)
                   (to_fset next1) d /\
                 succ v SUBSET to_fset visited3 /\
                 (!x:A.
                    ntp4vc_vstte12_bfs_closure
                      succ
                      (to_fset visited3) (to_fset current2)
                      (to_fset next1) x)
                 ==>
                 if to_fset current2 = ({}:A->bool) then
                   !o3:S.
                     to_fset o3 = ({}:A->bool) /\
                     (&(CARD (to_fset o3)):int) = (&0:int)
                     ==>
                     ntp4vc_vstte12_bfs_inv
                       succ s t
                       (to_fset visited3) (to_fset next1)
                       (to_fset o3) (d + (&1:int)) /\
                     (to_fset next1 = ({}:A->bool)
                      ==> to_fset o3 = ({}:A->bool)) /\
                     (!x:A.
                        ntp4vc_vstte12_bfs_closure
                          succ
                          (to_fset visited3) (to_fset next1)
                          (to_fset o3) x) /\
                     (&0:int) <= d + (&1:int)
                 else
                   ntp4vc_vstte12_bfs_inv
                     succ s t
                     (to_fset visited3) (to_fset current2)
                     (to_fset next1) d /\
                   (to_fset current2 = ({}:A->bool)
                    ==> to_fset next1 = ({}:A->bool)) /\
                   (!x:A.
                      ntp4vc_vstte12_bfs_closure
                        succ
                        (to_fset visited3) (to_fset current2)
                        (to_fset next1) x) /\
                   (&0:int) <= d))
       else
         !d1:int. ~ntp4vc_vstte12_bfs_path succ s t d1)`;;
