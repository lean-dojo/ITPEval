(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bellman_ford_BellmanFord_bellman_fordqtvc: the Bellman-Ford
  verification condition for relaxation passes, shortest-path distances,
  and detection of a reachable negative cycle. This file contains no proof.
*)

let statement =
 `!vertices:A->bool.
  !edges:(A#A)->bool.
  !source:A.
  !weight:A->A->int.
  !path:A->A list->A->bool.
  !path_weight:A list->A->int.
  !to_fset:S->(A#A)->bool.
  !choose:S->A#A.
  !contents:M->A->int option.
  !lookup:M->A->int option.
  !create:int option->M.
  !update:M->A->int option->M.
    let empty_edges = ({}:(A#A)->bool) in
    let ii_add =
      \(x:int option) (y:int option).
        if x = NONE \/ y = NONE then NONE
        else
          SOME
            ((@a:int. x = SOME a) +
             (@b:int. y = SOME b)) in
    let ii_lt =
      \(x:int option) (y:int option).
        if x = NONE then F
        else if y = NONE then T
        else
          (@a:int. x = SOME a) <
          (@b:int. y = SOME b) in
    let ii_le =
      \(x:int option) (y:int option).
        ii_lt x y \/ x = y in
    let negative_cycle =
      \v:A.
        v IN vertices /\
        (?l1:A list. path source l1 v) /\
        (?l2:A list.
           path v l2 v /\
           path_weight l2 v < (&0:int)) in
    let inv1 =
      \(map:M) (pass:int) (via:(A#A)->bool).
        !v:A.
          v IN vertices
          ==>
          if lookup map v = NONE then
            (!l:A list.
               path source l v
               ==> pass <= (&(LENGTH l):int)) /\
            (!u:A.
               (u,v) IN via
               ==>
               !lu:A list.
                 path source lu u
                 ==> pass <= (&(LENGTH lu):int))
          else
            let n = @n:int. lookup map v = SOME n in
            (?l:A list.
               path source l v /\
               path_weight l v = n) /\
            (!l:A list.
               path source l v
               ==> (&(LENGTH l):int) < pass
               ==> n <= path_weight l v) /\
            (!u:A.
             !l:A list.
               path source l u
               ==> (&(LENGTH l):int) < pass
               ==> (u,v) IN via
               ==> n <= path_weight l u + weight u v) in
    let inv2 =
      \(map:M) (via:(A#A)->bool).
        !u v:A.
          (u,v) IN via
          ==>
          ii_le
            (lookup map v)
            (ii_add (lookup map u) (SOME (weight u v))) in
    let shortest_paths =
      \map:M.
        !v:A.
          v IN vertices
          ==>
          if lookup map v = NONE then
            !l:A list. ~(path source l v)
          else
            let n = @n:int. lookup map v = SOME n in
            (?l:A list.
               path source l v /\
               path_weight l v = n) /\
            (!l:A list.
               path source l v
               ==> n <= path_weight l v) in
    let edge_pass =
      \(map:M) (pass:int).
        !es:S.
          to_fset es = edges
          ==>
          (to_fset es SUBSET edges /\
           inv1 map pass (edges DIFF to_fset es)) /\
          (!es1:S.
           !map2:M.
             to_fset es1 SUBSET edges /\
             inv1 map2 pass (edges DIFF to_fset es1)
             ==>
             if ~(to_fset es1 = empty_edges) then
               let via = edges DIFF to_fset es1 in
               ~(to_fset es1 = empty_edges) /\
               (!es2:S.
                  let chosen = choose es1 in
                  chosen IN to_fset es1 /\
                  to_fset es2 = to_fset es1 DELETE chosen
                  ==>
                  let u = FST chosen in
                  let v = SND chosen in
                  (((&1:int) <= pass /\
                    chosen IN edges /\
                    ~(chosen IN via)) /\
                   inv1 map2 pass via) /\
                  (!map3:M.
                     inv1 map3 pass (chosen INSERT via)
                     ==>
                     ((&0:int) <=
                        (&(CARD (to_fset es1)):int) /\
                      CARD (to_fset es2) <
                        CARD (to_fset es1)) /\
                     to_fset es2 SUBSET edges /\
                     inv1 map3 pass
                       (edges DIFF to_fset es2)))
             else
               inv1 map2 (pass + (&1:int)) empty_edges) in
    let final_edge_pass =
      \map:M.
        !es:S.
          to_fset es = edges
          ==>
          (to_fset es SUBSET edges /\
           inv2 map (edges DIFF to_fset es)) /\
          (!es1:S.
             to_fset es1 SUBSET edges /\
             inv2 map (edges DIFF to_fset es1)
             ==>
             if ~(to_fset es1 = empty_edges) then
               ~(to_fset es1 = empty_edges) /\
               (!es2:S.
                  let chosen = choose es1 in
                  chosen IN to_fset es1 /\
                  to_fset es2 = to_fset es1 DELETE chosen
                  ==>
                  let u = FST chosen in
                  let v = SND chosen in
                  let old_v = lookup map v in
                  old_v = contents map v
                  ==>
                  let old_u = lookup map u in
                  old_u = contents map u
                  ==>
                  if ii_lt
                       (ii_add old_u (SOME (weight u v)))
                       old_v
                  then
                    ?v1:A. negative_cycle v1
                  else
                    ((&0:int) <=
                       (&(CARD (to_fset es1)):int) /\
                     CARD (to_fset es2) <
                       CARD (to_fset es1)) /\
                    to_fset es2 SUBSET edges /\
                    inv2 map (edges DIFF to_fset es2))
             else
               shortest_paths map) in
    let initial_map =
      update (create (NONE:int option))
        source (SOME (&0:int)) in
    let last_pass =
      (&(CARD vertices):int) - (&1:int) in
    let background =
      (FINITE vertices /\
      FINITE edges /\
      (!es:S. FINITE (to_fset es)) /\
      (!x y:A.
         (x,y) IN edges
         ==> x IN vertices /\ y IN vertices) /\
      source IN vertices /\
      (!x z:A. (path x [] z <=> x = z)) /\
      (!x h:A.
       !tail:A list.
       !z:A.
         (path x (CONS h tail) z <=>
          h = x /\
          (?y:A.
             (x,y) IN edges /\
             path y tail z))) /\
      (!dst:A.
         path_weight [] dst = (&0:int)) /\
      (!x dst:A.
         path_weight [x] dst = weight x dst) /\
      (!x y:A.
       !tail:A list.
       !dst:A.
         path_weight (CONS x (CONS y tail)) dst =
           weight x y +
           path_weight (CONS y tail) dst) /\
      (!es:S.
         ~(to_fset es = empty_edges)
         ==> choose es IN to_fset es) /\
      (!value:int option.
       !x:A.
         contents (create value) x = value) /\
      (!map:M.
       !key:A.
         lookup map key = contents map key) /\
      (!map:M.
       !key:A.
       !value:int option.
       !x:A.
         contents (update map key value) x =
           (if x = key then value else contents map x))) in
    background
    ==>
    (((&1:int) <= last_pass + (&1:int)
      ==>
      inv1 initial_map (&1:int) empty_edges /\
      (!map1:M.
         (!pass:int.
            (((&1:int) <= pass /\ pass <= last_pass) /\
             inv1 map1 pass empty_edges)
            ==> edge_pass map1 pass) /\
         (inv1 map1 (last_pass + (&1:int)) empty_edges
          ==> final_edge_pass map1))) /\
     (last_pass + (&1:int) < (&1:int)
      ==> final_edge_pass initial_map))`;;
