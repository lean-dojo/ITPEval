(*
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/schorr_waite_SchorrWaite_schorr_waiteqtvc: the complete generated
  verification condition for the Schorr-Waite graph-marking algorithm,
  including its stack and path invariants, pointer-reversal transitions,
  lexicographic termination obligations, and final reachability property.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory pred_setTheory;

val sw_to_num_def = Define `
  sw_to_num (z : int) = if z < 0 then 0 else Num z`;

val sw_get_def = Define `
  sw_get (xs : 'a list) (i : int) =
    if sw_to_num i < LENGTH xs then EL (sw_to_num i) xs else ARB`;

val sw_update_def = Define `
  sw_update (f : 'a -> 'b) (x : 'a) (v : 'b) =
    \y. if y = x then v else f y`;

val sw_not_in_stack_def = Define `
  sw_not_in_stack (n : 'a) (stackNodes : 'a list) <=>
    !i : int.
      0 <= i /\ i < &(LENGTH stackNodes) ==>
      n <> sw_get stackNodes i`;

val sw_last_def = Define `
  sw_last (stackNodes : 'a list) =
    sw_get stackNodes (&(LENGTH stackNodes) - 1)`;

val sw_distinct_def = Define `
  sw_distinct (stackNodes : 'a list) <=>
    !i j : int.
      0 <= i /\ i < &(LENGTH stackNodes) /\
      0 <= j /\ j < &(LENGTH stackNodes) /\
      sw_get stackNodes i = sw_get stackNodes j ==>
      i = j`;

val sw_edge_def = Define `
  sw_edge (null : 'a) (left : 'a -> 'a) (right : 'a -> 'a)
          (x : 'a) (y : 'a) <=>
    x <> null /\ (left x = y \/ right x = y)`;

val (sw_path_rules, sw_path_ind, sw_path_cases) = Hol_reln `
  (!null left right x.
     sw_path null left right x x []) /\
  (!null left right x z y pathNodes.
     sw_edge null left right x z /\
     sw_path null left right z y pathNodes ==>
     sw_path null left right x y (x :: pathNodes))`;

val sw_reachable_def = Define `
  sw_reachable (null : 'a) (left : 'a -> 'a) (right : 'a -> 'a)
               (x : 'a) (y : 'a) <=>
    ?pathNodes. sw_path null left right x y pathNodes`;

val sw_variant_decreases_def = Define `
  sw_variant_decreases
      (oldUnmarked : 'a set) (oldCfalse : 'a set) (oldStack : 'a list)
      (newUnmarked : 'a set) (newCfalse : 'a set) (newStack : 'a list) <=>
    ((0 : int) <= &(CARD oldUnmarked) /\
     CARD newUnmarked < CARD oldUnmarked) \/
    (CARD newUnmarked = CARD oldUnmarked /\
     (((0 : int) <= &(CARD oldCfalse) /\
       CARD newCfalse < CARD oldCfalse) \/
      (CARD newCfalse = CARD oldCfalse /\
       (0 : int) <= &(LENGTH oldStack) /\
       LENGTH newStack < LENGTH oldStack)))`;

val sw_invariant_def = Define `
  sw_invariant
      (null : 'a) (graph : 'a set) (root : 'a)
      (left0 : 'a -> 'a) (right0 : 'a -> 'a)
      (stackNodes : 'a list) (p : 'a) (t : 'a)
      (pathNodes : 'a list) (pathFromRoot : 'a -> 'a list)
      (left : 'a -> 'a) (right : 'a -> 'a)
      (c : 'a -> bool) (m : 'a -> bool)
      (unmarked : 'a set) (cfalse : 'a set) <=>
    FINITE graph /\ FINITE unmarked /\ FINITE cfalse /\
    (!n.
       n IN graph ==>
       sw_not_in_stack n stackNodes \/
       ?i : int.
         0 <= i /\ i < &(LENGTH stackNodes) /\
         sw_get stackNodes i = n) /\
    sw_not_in_stack null stackNodes /\
    ((LENGTH stackNodes = 0) <=> (p = null)) /\
    (p <> null ==> p IN graph) /\
    (LENGTH stackNodes <> 0 ==> sw_get stackNodes 0 = p) /\
    (!n. n IN graph /\ ~m n ==> n IN unmarked) /\
    (!n. n IN graph /\ ~c n ==> n IN cfalse) /\
    (!i : int.
       0 <= i /\ i < &(LENGTH stackNodes) ==>
       sw_get stackNodes i IN graph) /\
    (!i : int.
       0 <= i /\ i < &(LENGTH stackNodes) - 1 ==>
       let p1 = sw_get stackNodes i in
       let p2 = sw_get stackNodes (i + 1) in
         (c p2 ==>
          left0 p2 = left p2 /\ right0 p2 = p1) /\
         (~c p2 ==>
          left0 p2 = p1 /\ right0 p2 = right p2)) /\
    pathFromRoot root = [] /\
    (!n.
       n IN graph /\ sw_not_in_stack n stackNodes ==>
       left n = left0 n /\ right n = right0 n) /\
    (LENGTH stackNodes <> 0 ==>
     let first = sw_last stackNodes in
       if c first then right first = null else left first = null) /\
    (LENGTH stackNodes <> 0 ==> sw_last stackNodes = root) /\
    (!k : int.
       0 <= k /\ k < &(LENGTH stackNodes) - 1 ==>
       let n = sw_get stackNodes k in
         if c n
         then right n = sw_get stackNodes (k + 1)
         else left n = sw_get stackNodes (k + 1)) /\
    (!i : int.
       0 <= i /\ i < &(LENGTH stackNodes) ==>
       m (sw_get stackNodes i)) /\
    sw_distinct stackNodes /\
    (!i : int.
       0 <= i /\ i < &(LENGTH stackNodes) ==>
       let n = sw_get stackNodes i in
         if c n then left n = left0 n else right n = right0 n) /\
    (p <> null ==>
     if c p then right0 p = t else left0 p = t) /\
    (!k : int.
       0 < k /\ k < &(LENGTH stackNodes) ==>
       let n = sw_get stackNodes k in
         if c n
         then sw_get stackNodes (k - 1) = right0 n
         else sw_get stackNodes (k - 1) = left0 n) /\
    (p <> null ==>
     sw_path null left0 right0 root p pathNodes) /\
    (!n.
       n IN graph /\ m n ==>
       sw_reachable null left0 right0 root n) /\
    (p = null ==> t = root) /\
    (!n.
       n IN graph /\ m n ==>
       sw_path null left0 right0 root n (pathFromRoot n)) /\
    (!n.
       n IN graph /\ n <> null /\ m n /\
       sw_not_in_stack n stackNodes ==>
       (left n <> null ==> m (left n)) /\
       (right n <> null ==> m (right n))) /\
    (!i : int.
       0 <= i /\ i < &(LENGTH stackNodes) ==>
       let n = sw_get stackNodes i in
         c n ==>
         (left n <> null ==> m (left n)) /\
         (right n <> null ==> m (right n)))`;

val sw_pop_or_swing_vc_def = Define `
  sw_pop_or_swing_vc
      (null : 'a) (graph : 'a set) (root : 'a)
      (left0 : 'a -> 'a) (right0 : 'a -> 'a)
      (stackNodes : 'a list) (p : 'a) (t : 'a)
      (pathNodes : 'a list) (pathFromRoot : 'a -> 'a list)
      (left : 'a -> 'a) (right : 'a -> 'a)
      (c : 'a -> bool) (m : 'a -> bool)
      (unmarked : 'a set) (cfalse : 'a set) <=>
    p <> null /\
    if c p then
      (0 : int) < &(LENGTH stackNodes) /\
      let newStack = DROP 1 stackNodes in
        ((!n.
            sw_not_in_stack n stackNodes ==>
            sw_not_in_stack n newStack) ==>
         sw_variant_decreases
           unmarked cfalse stackNodes unmarked cfalse newStack /\
         sw_invariant
           null graph root left0 right0
           newStack (right p) p (pathFromRoot (right p)) pathFromRoot
           left (sw_update right p t) c m unmarked cfalse)
    else
      sw_variant_decreases
        unmarked cfalse stackNodes
        unmarked (cfalse DELETE p) stackNodes /\
      sw_invariant
        null graph root left0 right0
        stackNodes p (right p) pathNodes pathFromRoot
        (sw_update left p t)
        (sw_update right p (left p))
        (sw_update c p T) m unmarked (cfalse DELETE p)`;

val sw_push_vc_def = Define `
  sw_push_vc
      (null : 'a) (graph : 'a set) (root : 'a)
      (left0 : 'a -> 'a) (right0 : 'a -> 'a)
      (stackNodes : 'a list) (p : 'a) (t : 'a)
      (pathNodes : 'a list) (pathFromRoot : 'a -> 'a list)
      (left : 'a -> 'a) (right : 'a -> 'a)
      (c : 'a -> bool) (m : 'a -> bool)
      (unmarked : 'a set) (cfalse : 'a set) <=>
    t <> null /\
    let newStack = t :: stackNodes in
      &(LENGTH newStack) = (1 : int) + &(LENGTH stackNodes) /\
      sw_get newStack 0 = t /\
      (!i : int.
         0 < i /\ i <= &(LENGTH stackNodes) ==>
         sw_get newStack i = sw_get stackNodes (i - 1)) ==>
      sw_variant_decreases
        unmarked cfalse stackNodes
        (unmarked DELETE t) (t INSERT cfalse) newStack /\
      (if t <> root then
         sw_invariant
           null graph root left0 right0
           newStack t (left t) (pathNodes ++ [p])
           (sw_update pathFromRoot t (pathNodes ++ [p]))
           (sw_update left t p) right
           (sw_update c t F) (sw_update m t T)
           (unmarked DELETE t) (t INSERT cfalse)
       else
         sw_invariant
           null graph root left0 right0
           newStack t (left t) []
           (sw_update pathFromRoot t [])
           (sw_update left t p) right
           (sw_update c t F) (sw_update m t T)
           (unmarked DELETE t) (t INSERT cfalse))`;

val sw_final_def = Define `
  sw_final
      (null : 'a) (graph : 'a set) (root : 'a)
      (left0 : 'a -> 'a) (right0 : 'a -> 'a)
      (left : 'a -> 'a) (right : 'a -> 'a)
      (m : 'a -> bool) <=>
    (!n.
       n IN graph ==>
       left n = left0 n /\ right n = right0 n) /\
    (!n.
       n IN graph /\ m n ==>
       sw_reachable null left0 right0 root n) /\
    m root /\
    (!n.
       n IN graph /\ m n ==>
       (left n <> null ==> m (left n)) /\
       (right n <> null ==> m (right n)))`;

val sw_loop_vc_def = Define `
  sw_loop_vc
      (null : 'a) (graph : 'a set) (root : 'a)
      (left0 : 'a -> 'a) (right0 : 'a -> 'a)
      (stackNodes : 'a list) (p : 'a) (t : 'a)
      (pathNodes : 'a list) (pathFromRoot : 'a -> 'a list)
      (left : 'a -> 'a) (right : 'a -> 'a)
      (c : 'a -> bool) (m : 'a -> bool)
      (unmarked : 'a set) (cfalse : 'a set) <=>
    !outerCondition.
      (if p <> null then outerCondition = T
       else if t <> null
            then outerCondition = (if m t then F else T)
            else outerCondition = F) ==>
      if outerCondition then
        !popCondition.
          (if t = null
           then popCondition = T
           else popCondition = m t) ==>
          if popCondition then
            sw_pop_or_swing_vc
              null graph root left0 right0
              stackNodes p t pathNodes pathFromRoot
              left right c m unmarked cfalse
          else
            sw_push_vc
              null graph root left0 right0
              stackNodes p t pathNodes pathFromRoot
              left right c m unmarked cfalse
      else
        sw_final null graph root left0 right0 left right m`;

val schorr_waite_SchorrWaite_schorr_waite_vc = ``
  !(null : 'loc) root
    (graph : 'loc set)
    (left0 : 'loc -> 'loc) (right0 : 'loc -> 'loc)
    (c0 : 'loc -> bool) (m0 : 'loc -> bool)
    (pathFromRoot0 : 'loc -> 'loc list).
    FINITE graph /\
    root IN graph /\
    root <> null /\
    (!n.
       n IN graph ==>
       n <> null /\
       (left0 n = null \/ left0 n IN graph) /\
       (right0 n = null \/ right0 n IN graph)) /\
    (!n. n IN graph ==> ~m0 n) ==>
    root <> null /\
    sw_invariant
      null graph root left0 right0
      [] null root []
      (sw_update pathFromRoot0 root [])
      left0 right0 c0 m0 graph graph /\
    (!stackNodes p t pathNodes pathFromRoot left right c m
      (unmarked : 'loc set) (cfalse : 'loc set).
       sw_invariant
         null graph root left0 right0
         stackNodes p t pathNodes pathFromRoot
         left right c m unmarked cfalse ==>
       sw_loop_vc
         null graph root left0 right0
         stackNodes p t pathNodes pathFromRoot
         left right c m unmarked cfalse)
``;
