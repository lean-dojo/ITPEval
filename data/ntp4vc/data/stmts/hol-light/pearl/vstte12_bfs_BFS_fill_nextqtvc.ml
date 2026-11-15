(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_bfs_BFS_fill_nextqtvc: the breadth-first-search fill-next
  verification condition preserving successor processing, visited/current/next
  frontier invariants, closure, set updates, and loop progress. This file
  contains no proof.
*)

let ntp4vc_vstte12_bfs_fill_path_RULES,
    ntp4vc_vstte12_bfs_fill_path_INDUCT,
    ntp4vc_vstte12_bfs_fill_path_CASES =
  new_inductive_definition
   `(!succ:A->A->bool.
     !v:A.
       ntp4vc_vstte12_bfs_fill_path succ v v (&0:int)) /\
    (!succ:A->A->bool.
     !v1 v2 v3:A.
     !n:int.
       ntp4vc_vstte12_bfs_fill_path succ v1 v2 n /\
       v3 IN succ v2
       ==> ntp4vc_vstte12_bfs_fill_path
             succ v1 v3 (n + (&1:int)))`;;

let ntp4vc_vstte12_bfs_fill_shortest_path = new_definition
 `ntp4vc_vstte12_bfs_fill_shortest_path
    (succ:A->A->bool) (v1:A) (v2:A) (n:int) <=>
    ntp4vc_vstte12_bfs_fill_path succ v1 v2 n /\
    (!m:int.
       m < n
       ==> ~ntp4vc_vstte12_bfs_fill_path succ v1 v2 m)`;;

let ntp4vc_vstte12_bfs_fill_inv = new_definition
 `ntp4vc_vstte12_bfs_fill_inv
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
       ==> ntp4vc_vstte12_bfs_fill_shortest_path succ s x d) /\
    next SUBSET visited /\
    (!x:A.
       x IN next
       ==> ntp4vc_vstte12_bfs_fill_shortest_path
             succ s x (d + (&1:int))) /\
    (!x:A.
     !m:int.
       ntp4vc_vstte12_bfs_fill_path succ s x m
       ==> m <= d
       ==> x IN visited) /\
    (!x:A.
       x IN visited
       ==> ?m:int.
             ntp4vc_vstte12_bfs_fill_path succ s x m /\
             m <= d + (&1:int)) /\
    (!x:A.
       ntp4vc_vstte12_bfs_fill_shortest_path
         succ s x (d + (&1:int))
       ==> x IN next \/ ~(x IN visited)) /\
    (t IN visited ==> t IN current \/ t IN next)`;;

let ntp4vc_vstte12_bfs_fill_closure = new_definition
 `ntp4vc_vstte12_bfs_fill_closure
    (succ:A->A->bool)
    (visited:A->bool)
    (current:A->bool)
    (next:A->bool)
    (x:A) <=>
    x IN visited
    ==> ~(x IN current)
    ==> ~(x IN next)
    ==> !y:A. y IN succ x ==> y IN visited`;;

let statement =
 `!succ:A->A->bool.
  !to_fset:S->A->bool.
  !choose:S->A.
  !s t:A.
  !visited current next:S.
  !d:int.
  !v:A.
  !acc:S.
    (!x:A. FINITE (succ x))
    ==>
    (!q:S. FINITE (to_fset q))
    ==>
    (!q:S.
       ~(to_fset q = ({}:A->bool))
       ==> choose q IN to_fset q)
    ==>
    ntp4vc_vstte12_bfs_fill_inv
      succ s t
      (to_fset visited) (to_fset current) (to_fset next) d
    ==>
    ntp4vc_vstte12_bfs_fill_shortest_path succ s v d
    ==>
    (!x:A.
       ~(x = v)
       ==> ntp4vc_vstte12_bfs_fill_closure
             succ
             (to_fset visited) (to_fset current) (to_fset next) x)
    ==>
    to_fset acc = succ v
    ==>
    ntp4vc_vstte12_bfs_fill_inv
      succ s t
      (to_fset visited) (to_fset current) (to_fset next) d /\
    to_fset acc SUBSET succ v /\
    (succ v DIFF to_fset acc) SUBSET to_fset visited /\
    (!x:A.
       ~(x = v)
       ==> ntp4vc_vstte12_bfs_fill_closure
             succ
             (to_fset visited) (to_fset current) (to_fset next) x) /\
    (!acc1 next1 visited1:S.
       ntp4vc_vstte12_bfs_fill_inv
         succ s t
         (to_fset visited1) (to_fset current) (to_fset next1) d /\
       to_fset acc1 SUBSET succ v /\
       (succ v DIFF to_fset acc1) SUBSET to_fset visited1 /\
       (!x:A.
          ~(x = v)
          ==> ntp4vc_vstte12_bfs_fill_closure
                succ
                (to_fset visited1) (to_fset current)
                (to_fset next1) x)
       ==>
       if ~(to_fset acc1 = ({}:A->bool)) then
         ~(to_fset acc1 = ({}:A->bool)) /\
         (!acc2:S.
            let w = choose acc1 in
            w IN to_fset acc1 /\
            to_fset acc2 = to_fset acc1 DELETE w
            ==>
            if ~(w IN to_fset visited1) then
              !visited2:S.
                to_fset visited2 =
                  w INSERT to_fset visited1 /\
                (if w IN to_fset visited1 then
                   CARD (to_fset visited2) =
                   CARD (to_fset visited1)
                 else
                   (&(CARD (to_fset visited2)):int) =
                   (&(CARD (to_fset visited1)):int) + (&1:int))
                ==>
                !next2:S.
                  to_fset next2 =
                    w INSERT to_fset next1 /\
                  (if w IN to_fset next1 then
                     CARD (to_fset next2) =
                     CARD (to_fset next1)
                   else
                     (&(CARD (to_fset next2)):int) =
                     (&(CARD (to_fset next1)):int) + (&1:int))
                  ==>
                  ((&0:int) <=
                     (&(CARD (to_fset acc1)):int) /\
                   CARD (to_fset acc2) <
                     CARD (to_fset acc1)) /\
                  ntp4vc_vstte12_bfs_fill_inv
                    succ s t
                    (to_fset visited2) (to_fset current)
                    (to_fset next2) d /\
                  to_fset acc2 SUBSET succ v /\
                  (succ v DIFF to_fset acc2) SUBSET
                    to_fset visited2 /\
                  (!x:A.
                     ~(x = v)
                     ==> ntp4vc_vstte12_bfs_fill_closure
                           succ
                           (to_fset visited2) (to_fset current)
                           (to_fset next2) x)
            else
              ((&0:int) <=
                 (&(CARD (to_fset acc1)):int) /\
               CARD (to_fset acc2) <
                 CARD (to_fset acc1)) /\
              ntp4vc_vstte12_bfs_fill_inv
                succ s t
                (to_fset visited1) (to_fset current)
                (to_fset next1) d /\
              to_fset acc2 SUBSET succ v /\
              (succ v DIFF to_fset acc2) SUBSET
                to_fset visited1 /\
              (!x:A.
                 ~(x = v)
                 ==> ntp4vc_vstte12_bfs_fill_closure
                       succ
                       (to_fset visited1) (to_fset current)
                       (to_fset next1) x))
       else
         ntp4vc_vstte12_bfs_fill_inv
           succ s t
           (to_fset visited1) (to_fset current) (to_fset next1) d /\
         succ v SUBSET to_fset visited1 /\
         (!x:A.
            ntp4vc_vstte12_bfs_fill_closure
              succ
              (to_fset visited1) (to_fset current)
              (to_fset next1) x))`;;
