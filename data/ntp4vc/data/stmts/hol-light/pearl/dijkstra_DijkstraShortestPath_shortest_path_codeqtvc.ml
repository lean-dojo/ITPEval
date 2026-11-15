(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/dijkstra_DijkstraShortestPath_shortest_path_codeqtvc: the Dijkstra
  shortest-path verification condition for initialization, vertex extraction,
  edge relaxation, loop invariants, and final shortest-path results. This file
  contains no proof.
*)

let statement =
 `!vertices:A->bool.
  !successors:A->A->bool.
  !weight:A->A->int.
  !to_fset:S->A->bool.
  !choose:S->A.
  !lookup:M->A->int.
  !update:M->A->int->M.
  !path_vertices:A->A list->A->bool.
  !path_weight:A list->A->int.
  !src dst:A.
  !visited q:S.
  !d:M.
    let empty_vertices = ({}:A->bool) in
    let path =
      \(x:A) (y:A) (distance:int).
        ?nodes:A list.
          path_vertices x nodes y /\
          path_weight nodes y = distance in
    let shortest_path =
      \(x:A) (y:A) (distance:int).
        path x y distance /\
        (!distance':int.
           path x y distance'
           ==> distance <= distance') in
    let is_min =
      \(m:A) (queue:S) (distances:M).
        m IN to_fset queue /\
        (!x:A.
           x IN to_fset queue
           ==> lookup distances m <= lookup distances x) in
    let inv_src =
      \(source:A) (settled:S) (queue:S).
        source IN to_fset settled \/
        source IN to_fset queue in
    let inv =
      \(source:A) (settled:S) (queue:S) (distances:M).
        inv_src source settled queue /\
        lookup distances source = (&0:int) /\
        to_fset settled SUBSET vertices /\
        to_fset queue SUBSET vertices /\
        (!v1:A.
           v1 IN to_fset queue
           ==> ~(v1 IN to_fset settled)) /\
        (!v1:A.
           v1 IN to_fset settled
           ==> shortest_path source v1 (lookup distances v1)) /\
        (!v1:A.
           v1 IN to_fset queue
           ==> path source v1 (lookup distances v1)) in
    let inv_succ =
      \(source:A) (settled:S) (queue:S) (distances:M).
        !x:A.
          x IN to_fset settled
          ==>
          !y:A.
            y IN successors x
            ==>
            (y IN to_fset settled \/ y IN to_fset queue) /\
            lookup distances y <=
              lookup distances x + weight x y in
    let inv_succ2 =
      \(source:A) (settled:S) (queue:S) (distances:M)
       (u:A) (remaining:S).
        !x:A.
          x IN to_fset settled
          ==>
          !y:A.
            y IN successors x
            ==>
            (~(x = u) \/
             (x = u /\ ~(y IN to_fset remaining)))
            ==>
            (y IN to_fset settled \/ y IN to_fset queue) /\
            lookup distances y <=
              lookup distances x + weight x y in
    let background =
      (FINITE vertices /\
       (!x:A. successors x SUBSET vertices) /\
       (!x y:A. (&0:int) <= weight x y) /\
       (!s:S. FINITE (to_fset s)) /\
       (!s:S.
          ~(to_fset s = empty_vertices)
          ==> choose s IN to_fset s) /\
       (!map:M.
        !key:A.
        !value:int.
        !x:A.
          lookup (update map key value) x =
          (if x = key then value else lookup map x)) /\
       (!x z:A.
          (path_vertices x [] z <=> x = z)) /\
       (!x h:A.
        !tail:A list.
        !z:A.
          (path_vertices x (CONS h tail) z <=>
           h = x /\
           (?y:A.
              y IN successors x /\
              path_vertices y tail z))) /\
       (!z:A.
          path_weight [] z = (&0:int)) /\
       (!x z:A.
          path_weight [x] z = weight x z) /\
       (!x y:A.
        !tail:A list.
        !z:A.
          path_weight (CONS x (CONS y tail)) z =
          weight x y +
          path_weight (CONS y tail) z)) in
    background
    ==>
    src IN vertices
    ==>
    dst IN vertices
    ==>
    to_fset visited = empty_vertices
    ==>
    to_fset q = src INSERT empty_vertices
    ==>
    inv src visited q (update d src (&0:int)) /\
    inv_succ src visited q (update d src (&0:int)) /\
    (!m:A.
       is_min m q (update d src (&0:int))
       ==>
       !x:A.
       !dx:int.
         path src x dx
         ==>
         dx < lookup (update d src (&0:int)) m
         ==>
         x IN to_fset visited) /\
    (!q1:S.
     !d1:M.
     !visited1:S.
       inv src visited1 q1 d1 /\
       inv_succ src visited1 q1 d1 /\
       (!m:A.
          is_min m q1 d1
          ==>
          !x:A.
          !dx:int.
            path src x dx
            ==>
            dx < lookup d1 m
            ==>
            x IN to_fset visited1)
       ==>
       if ~(to_fset q1 = empty_vertices) then
         ~(to_fset q1 = empty_vertices) /\
         (!q2:S.
          !u:A.
            is_min u q1 d1 /\
            to_fset q2 = to_fset q1 DELETE u
            ==>
            !visited2:S.
              to_fset visited2 =
                u INSERT to_fset visited1 /\
              (if u IN to_fset visited1 then
                 CARD (to_fset visited2) =
                 CARD (to_fset visited1)
               else
                 (&(CARD (to_fset visited2)):int) =
                 (&(CARD (to_fset visited1)):int) +
                 (&1:int))
              ==>
              !su:S.
                to_fset su = successors u
                ==>
                (to_fset su SUBSET successors u /\
                 inv src visited2 q2 d1 /\
                 inv_succ2 src visited2 q2 d1 u su) /\
                (!su1:S.
                 !q3:S.
                 !d2:M.
                   to_fset su1 SUBSET successors u /\
                   inv src visited2 q3 d2 /\
                   inv_succ2 src visited2 q3 d2 u su1
                   ==>
                   if ~(to_fset su1 = empty_vertices) then
                     ~(to_fset su1 = empty_vertices) /\
                     (!su2:S.
                        let v1 = choose su1 in
                        v1 IN to_fset su1 /\
                        to_fset su2 =
                          to_fset su1 DELETE v1
                        ==>
                        !q4:S.
                        !d3:M.
                          ((v1 IN to_fset visited2 /\
                            q4 = q3 /\
                            d3 = d2) \/
                           (v1 IN to_fset q4 /\
                            lookup d3 v1 <=
                              lookup d3 u + weight u v1 /\
                            q4 = q3 /\
                            d3 = d2) \/
                           (v1 IN to_fset q4 /\
                            lookup d2 u + weight u v1 <
                              lookup d2 v1 /\
                            q4 = q3 /\
                            d3 =
                              update d2 v1
                                (lookup d2 u + weight u v1)) \/
                           (~(v1 IN to_fset visited2) /\
                            ~(v1 IN to_fset q3) /\
                            to_fset q4 =
                              v1 INSERT to_fset q3 /\
                            d3 =
                              update d2 v1
                                (lookup d2 u + weight u v1)))
                          ==>
                          ((&0:int) <=
                             (&(CARD (to_fset su1)):int) /\
                           CARD (to_fset su2) <
                             CARD (to_fset su1)) /\
                          to_fset su2 SUBSET successors u /\
                          inv src visited2 q4 d3 /\
                          inv_succ2
                            src visited2 q4 d3 u su2)
                   else
                     (((&0:int) <=
                         (&(CARD vertices):int) -
                         (&(CARD (to_fset visited1)):int) /\
                       (&(CARD vertices):int) -
                         (&(CARD (to_fset visited2)):int) <
                       (&(CARD vertices):int) -
                         (&(CARD (to_fset visited1)):int)) /\
                      inv src visited2 q3 d2 /\
                      inv_succ src visited2 q3 d2 /\
                      (!m:A.
                         is_min m q3 d2
                         ==>
                         !x:A.
                         !dx:int.
                           path src x dx
                           ==>
                           dx < lookup d2 m
                           ==>
                           x IN to_fset visited2))))
       else
         (!v1:A.
            v1 IN to_fset visited1
            ==>
            shortest_path src v1 (lookup d1 v1)) /\
         (!v1:A.
            ~(v1 IN to_fset visited1)
            ==>
            !dv:int.
              ~(path src v1 dv)))`;;
