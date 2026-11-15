(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/schorr_waite_SchorrWaite_schorr_waiteqtvc: the generated
  verification condition for the Schorr-Waite graph-marking algorithm,
  including its stack, path, pointer-restoration, and termination invariants.
  This file contains no proof.
*)

let schorr_waite_int_index = new_definition
 `schorr_waite_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let schorr_waite_nth = new_definition
 `schorr_waite_nth (xs:A list) (i:int) =
    if schorr_waite_int_index i < LENGTH xs
    then EL (schorr_waite_int_index i) xs
    else ARB`;;

let schorr_waite_update = new_definition
 `schorr_waite_update (f:A->B) (x:A) (y:B) =
    \z:A. if z = x then y else f z`;;

let schorr_waite_not_in_stack = new_definition
 `schorr_waite_not_in_stack (n:A) (stack:A list) <=>
    !i:int.
      (&0:int) <= i /\ i < (&(LENGTH stack):int)
      ==> ~(n = schorr_waite_nth stack i)`;;

let schorr_waite_last = new_definition
 `schorr_waite_last (stack:A list) =
    schorr_waite_nth stack ((&(LENGTH stack):int) - (&1:int))`;;

let schorr_waite_distinct = new_definition
 `schorr_waite_distinct (stack:A list) <=>
    !i j:int.
      (&0:int) <= i /\ i < (&(LENGTH stack):int)
      ==>
      (&0:int) <= j /\ j < (&(LENGTH stack):int)
      ==>
      ~(i = j)
      ==>
      ~(schorr_waite_nth stack i = schorr_waite_nth stack j)`;;

let schorr_waite_edge = new_definition
 `schorr_waite_edge
    (null:A) (x:A) (y:A) (left:A->A) (right:A->A) <=>
    ~(x = null) /\ (left x = y \/ right x = y)`;;

let schorr_waite_path =
  new_recursive_definition list_RECURSION
   `(!null:A.
     !left right:A->A.
     !x y:A.
       schorr_waite_path null left right x y [] <=> x = y) /\
    (!null:A.
     !left right:A->A.
     !x y h:A.
     !tail:A list.
       schorr_waite_path null left right x y (CONS h tail) <=>
       h = x /\
       (?z:A.
          schorr_waite_edge null x z left right /\
          schorr_waite_path null left right z y tail))`;;

let schorr_waite_reachable = new_definition
 `schorr_waite_reachable
    (null:A) (left:A->A) (right:A->A) (x:A) (y:A) <=>
    ?pth:A list. schorr_waite_path null left right x y pth`;;

let schorr_waite_invariant = new_definition
 `schorr_waite_invariant
    (null:A)
    (root:A)
    (graph:A->bool)
    (left_initial:A->A)
    (right_initial:A->A)
    (c_false_nodes:A->bool)
    (unmarked_nodes:A->bool)
    (pth:A list)
    (stack:A list)
    (p:A)
    (t:A)
    (path_from_root:A->A list)
    (right:A->A)
    (left:A->A)
    (c:A->bool)
    (m:A->bool) <=>
    (!n:A.
       n IN graph
       ==>
       schorr_waite_not_in_stack n stack \/
       (?i:int. schorr_waite_nth stack i = n)) /\
    schorr_waite_not_in_stack null stack /\
    (((&(LENGTH stack):int) = (&0:int)) <=> p = null) /\
    (~(p = null) ==> p IN graph) /\
    (~((&(LENGTH stack):int) = (&0:int))
     ==> schorr_waite_nth stack (&0:int) = p) /\
    (!n:A.
       n IN graph
       ==> ~(m n = T)
       ==> n IN unmarked_nodes) /\
    (!n:A.
       n IN graph
       ==> ~(c n = T)
       ==> n IN c_false_nodes) /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH stack):int)
       ==> schorr_waite_nth stack i IN graph) /\
    (!i:int.
       (&0:int) <= i /\
       i < (&(LENGTH stack):int) - (&1:int)
       ==>
       let p1 = schorr_waite_nth stack i in
       let p2 = schorr_waite_nth stack (i + (&1:int)) in
       (c p2 = T
        ==> left_initial p2 = left p2 /\ right_initial p2 = p1) /\
       (~(c p2 = T)
        ==> left_initial p2 = p1 /\ right_initial p2 = right p2)) /\
    path_from_root root = [] /\
    (!n:A.
       n IN graph
       ==> schorr_waite_not_in_stack n stack
       ==> left n = left_initial n /\ right n = right_initial n) /\
    (~((&(LENGTH stack):int) = (&0:int))
     ==>
     let first = schorr_waite_last stack in
     if c first = T then right first = null else left first = null) /\
    (~((&(LENGTH stack):int) = (&0:int))
     ==> schorr_waite_last stack = root) /\
    (!k:int.
       (&0:int) <= k /\
       k < (&(LENGTH stack):int) - (&1:int)
       ==>
       if c (schorr_waite_nth stack k) = T
       then
         right (schorr_waite_nth stack k) =
         schorr_waite_nth stack (k + (&1:int))
       else
         left (schorr_waite_nth stack k) =
         schorr_waite_nth stack (k + (&1:int))) /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH stack):int)
       ==> m (schorr_waite_nth stack i) = T) /\
    schorr_waite_distinct stack /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH stack):int)
       ==>
       let n = schorr_waite_nth stack i in
       if c n = T
       then left n = left_initial n
       else right n = right_initial n) /\
    (~((&(LENGTH stack):int) = (&0:int))
     ==>
     if c p = T then right_initial p = t else left_initial p = t) /\
    (!k:int.
       (&0:int) < k /\ k < (&(LENGTH stack):int)
       ==>
       let n = schorr_waite_nth stack k in
       if c n = T
       then schorr_waite_nth stack (k - (&1:int)) = right_initial n
       else schorr_waite_nth stack (k - (&1:int)) = left_initial n) /\
    (~(p = null)
     ==> schorr_waite_path
           null left_initial right_initial root p pth) /\
    (!n:A.
       n IN graph
       ==> m n = T
       ==> schorr_waite_reachable
             null left_initial right_initial root n) /\
    (p = null ==> t = root) /\
    (!n:A.
       n IN graph
       ==> m n = T
       ==> schorr_waite_path
             null left_initial right_initial root n (path_from_root n)) /\
    (!n:A.
       n IN graph
       ==> ~(n = null)
       ==> m n = T
       ==> schorr_waite_not_in_stack n stack
       ==>
       (~(left n = null) ==> m (left n) = T) /\
       (~(right n = null) ==> m (right n) = T)) /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH stack):int)
       ==>
       let n = schorr_waite_nth stack i in
       c n = T
       ==>
       (~(left n = null) ==> m (left n) = T) /\
       (~(right n = null) ==> m (right n) = T))`;;

let schorr_waite_pop_variant = new_definition
 `schorr_waite_pop_variant
    (unmarked_nodes:A->bool)
    (c_false_nodes:A->bool)
    (stack:A list)
    (stack1:A list) <=>
    ((&0:int) <= (&(CARD unmarked_nodes):int) /\
     (&(CARD unmarked_nodes):int) < (&(CARD unmarked_nodes):int)) \/
    ((&0:int) <= (&(CARD c_false_nodes):int) /\
     (&(CARD c_false_nodes):int) < (&(CARD c_false_nodes):int)) \/
    ((&0:int) <= (&(LENGTH stack):int) /\
     (&(LENGTH stack1):int) < (&(LENGTH stack):int))`;;

let schorr_waite_swing_variant = new_definition
 `schorr_waite_swing_variant
    (unmarked_nodes:A->bool)
    (c_false_nodes:A->bool)
    (p:A)
    (stack:A list) <=>
    ((&0:int) <= (&(CARD unmarked_nodes):int) /\
     (&(CARD unmarked_nodes):int) < (&(CARD unmarked_nodes):int)) \/
    ((&0:int) <= (&(CARD c_false_nodes):int) /\
     (&(CARD (c_false_nodes DELETE p)):int) <
     (&(CARD c_false_nodes):int)) \/
    (CARD c_false_nodes = CARD (c_false_nodes DELETE p) /\
     (&0:int) <= (&(LENGTH stack):int) /\
     (&(LENGTH stack):int) < (&(LENGTH stack):int))`;;

let schorr_waite_push_variant = new_definition
 `schorr_waite_push_variant
    (unmarked_nodes:A->bool)
    (c_false_nodes:A->bool)
    (t:A)
    (stack:A list)
    (stack1:A list) <=>
    ((&0:int) <= (&(CARD unmarked_nodes):int) /\
     (&(CARD (unmarked_nodes DELETE t)):int) <
     (&(CARD unmarked_nodes):int)) \/
    (CARD unmarked_nodes = CARD (unmarked_nodes DELETE t) /\
     (((&0:int) <= (&(CARD c_false_nodes):int) /\
       (&(CARD (t INSERT c_false_nodes)):int) <
       (&(CARD c_false_nodes):int)) \/
      (CARD c_false_nodes = CARD (t INSERT c_false_nodes) /\
       (&0:int) <= (&(LENGTH stack):int) /\
       (&(LENGTH stack1):int) < (&(LENGTH stack):int))))`;;

let schorr_waite_exit = new_definition
 `schorr_waite_exit
    (null:A)
    (root:A)
    (graph:A->bool)
    (left_initial:A->A)
    (right_initial:A->A)
    (left:A->A)
    (right:A->A)
    (m:A->bool) <=>
    (!n:A.
       n IN graph
       ==> left_initial n = left n /\ right_initial n = right n) /\
    (!n:A.
       n IN graph
       ==> m n = T
       ==> schorr_waite_reachable
             null left_initial right_initial root n) /\
    m root = T /\
    (!n:A.
       n IN graph
       ==> m n = T
       ==>
       !ch:A.
         schorr_waite_edge null n ch left right
         ==> ~(ch = null)
         ==> m ch = T)`;;

let schorr_waite_body_vc = new_definition
 `schorr_waite_body_vc
    (null:A)
    (root:A)
    (graph:A->bool)
    (left_initial:A->A)
    (right_initial:A->A)
    (c_false_nodes:A->bool)
    (unmarked_nodes:A->bool)
    (pth:A list)
    (stack:A list)
    (p:A)
    (t:A)
    (path_from_root:A->A list)
    (right:A->A)
    (left:A->A)
    (c:A->bool)
    (m:A->bool) <=>
    if ~(p = null) \/ (~(t = null) /\ ~(m t = T)) then
      if t = null \/ m t = T then
        ~(p = null) /\
        if c p = T then
          (&0:int) < (&(LENGTH stack):int) /\
          (let stack1 = TL stack in
           (!n:A.
              schorr_waite_not_in_stack n stack
              ==> schorr_waite_not_in_stack n stack1)
           ==>
           ~(p = null) /\
           ~(p = null) /\
           schorr_waite_pop_variant
             unmarked_nodes c_false_nodes stack stack1 /\
           schorr_waite_invariant
             null root graph left_initial right_initial
             c_false_nodes unmarked_nodes
             (path_from_root (right p))
             stack1
             (right p)
             p
             path_from_root
             (schorr_waite_update right p t)
             left
             c
             m)
        else
          ~(p = null) /\
          ~(p = null) /\
          ~(p = null) /\
          ~(p = null) /\
          ~(p = null) /\
          schorr_waite_swing_variant
            unmarked_nodes c_false_nodes p stack /\
          schorr_waite_invariant
            null root graph left_initial right_initial
            (c_false_nodes DELETE p)
            unmarked_nodes
            pth
            stack
            p
            (right p)
            path_from_root
            (schorr_waite_update right p (left p))
            (schorr_waite_update left p t)
            (schorr_waite_update c p T)
            m
      else
        let stack1 = CONS t stack in
        ((&(LENGTH stack1):int) =
           (&1:int) + (&(LENGTH stack):int) /\
         schorr_waite_nth stack1 (&0:int) = t /\
         (!i:int.
            (&0:int) < i /\ i <= (&(LENGTH stack):int)
            ==>
            schorr_waite_nth stack1 i =
            schorr_waite_nth stack (i - (&1:int))))
        ==>
        ~(t = null) /\
        ~(t = null) /\
        ~(t = null) /\
        if ~(t = root) then
          ~(t = null) /\
          ~(t = null) /\
          schorr_waite_push_variant
            unmarked_nodes c_false_nodes t stack stack1 /\
          schorr_waite_invariant
            null root graph left_initial right_initial
            (t INSERT c_false_nodes)
            (unmarked_nodes DELETE t)
            (APPEND pth (CONS p []))
            stack1
            t
            (left t)
            (schorr_waite_update
               path_from_root t (APPEND pth (CONS p [])))
            right
            (schorr_waite_update left t p)
            (schorr_waite_update c t F)
            (schorr_waite_update m t T)
        else
          ~(t = null) /\
          ~(t = null) /\
          schorr_waite_push_variant
            unmarked_nodes c_false_nodes t stack stack1 /\
          schorr_waite_invariant
            null root graph left_initial right_initial
            (t INSERT c_false_nodes)
            (unmarked_nodes DELETE t)
            []
            stack1
            t
            (left t)
            (schorr_waite_update path_from_root t [])
            right
            (schorr_waite_update left t p)
            (schorr_waite_update c t F)
            (schorr_waite_update m t T)
    else
      schorr_waite_exit
        null root graph left_initial right_initial left right m`;;

let statement =
 `!null:A.
  !root:A.
  !graph:A->bool.
  !left_initial right_initial:A->A.
  !m c:A->bool.
  !path_from_root:A->A list.
    FINITE graph
    ==>
    ~(root = null)
    ==>
    root IN graph
    ==>
    (!n:A.
       n IN graph
       ==>
       ~(n = null) /\
       (left_initial n = null \/ left_initial n IN graph) /\
       (right_initial n = null \/ right_initial n IN graph))
    ==>
    (!x:A. x IN graph ==> ~(m x = T))
    ==>
    ~(root = null) /\
    schorr_waite_invariant
      null root graph left_initial right_initial
      graph
      graph
      []
      []
      null
      root
      (schorr_waite_update path_from_root root [])
      right_initial
      left_initial
      c
      m /\
    (!c_false_nodes unmarked_nodes:A->bool.
     !pth stack:A list.
     !p t:A.
     !path_from_root1:A->A list.
     !right left:A->A.
     !c1 m1:A->bool.
       FINITE c_false_nodes /\ FINITE unmarked_nodes
       ==>
       schorr_waite_invariant
         null root graph left_initial right_initial
         c_false_nodes
         unmarked_nodes
         pth
         stack
         p
         t
         path_from_root1
         right
         left
         c1
         m1
       ==>
       schorr_waite_body_vc
         null root graph left_initial right_initial
         c_false_nodes
         unmarked_nodes
         pth
         stack
         p
         t
         path_from_root1
         right
         left
         c1
         m1)`;;
