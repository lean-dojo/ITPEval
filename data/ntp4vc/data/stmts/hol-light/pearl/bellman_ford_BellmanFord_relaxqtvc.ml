(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bellman_ford_BellmanFord_relaxqtvc: the Bellman-Ford edge-relaxation
  verification condition preserving the pass invariant after processing a
  previously unprocessed edge. This file contains no proof.
*)

let statement =
 `!vertices:A->bool.
  !edges:(A#A)->bool.
  !source:A.
  !weight:A->A->int.
  !path:A->A list->A->bool.
  !path_weight:A list->A->int.
  !contents:M->A->int option.
  !lookup:M->A->int option.
  !update:M->A->int option->M.
  !pass:int.
  !u v:A.
  !via:(A#A)->bool.
  !map:M.
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
    let inv1 =
      \(map1:M) (pass1:int) (via1:(A#A)->bool).
        !w:A.
          w IN vertices
          ==>
          if lookup map1 w = NONE then
            (!l:A list.
               path source l w
               ==> pass1 <= (&(LENGTH l):int)) /\
            (!x:A.
               (x,w) IN via1
               ==>
               !lx:A list.
                 path source lx x
                 ==> pass1 <= (&(LENGTH lx):int))
          else
            let n = @n:int. lookup map1 w = SOME n in
            (?l:A list.
               path source l w /\
               path_weight l w = n) /\
            (!l:A list.
               path source l w
               ==> (&(LENGTH l):int) < pass1
               ==> n <= path_weight l w) /\
            (!x:A.
             !l:A list.
               path source l x
               ==> (&(LENGTH l):int) < pass1
               ==> (x,w) IN via1
               ==> n <= path_weight l x + weight x w) in
    let background =
      (FINITE vertices /\
       FINITE edges /\
       FINITE via /\
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
       (!map1:M.
        !key:A.
          lookup map1 key = contents map1 key) /\
       (!map1:M.
        !key:A.
        !value:int option.
        !x:A.
          contents (update map1 key value) x =
            (if x = key then value else contents map1 x))) in
    background
    ==>
    (&1:int) <= pass
    ==>
    (u,v) IN edges
    ==>
    ~((u,v) IN via)
    ==>
    inv1 map pass via
    ==>
    let old_u = lookup map u in
    old_u = contents map u
    ==>
    let candidate = ii_add old_u (SOME (weight u v)) in
    let old_v = lookup map v in
    old_v = contents map v
    ==>
    if ii_lt candidate old_v then
      inv1 (update map v candidate) pass ((u,v) INSERT via)
    else
      inv1 map pass ((u,v) INSERT via)`;;
