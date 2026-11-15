(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bellman_ford_BellmanFord_relaxqtvc: a Bellman-Ford verification
  condition stating that relaxing one previously unprocessed edge preserves
  the pass invariant over a finite weighted directed graph. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory pred_setTheory;

Datatype:
  bf_relax_intinf = BFRelaxFinite int | BFRelaxInfinite
End

val bf_relax_intinf_add_def = Define `
  (bf_relax_intinf_add BFRelaxInfinite y = BFRelaxInfinite) /\
  (bf_relax_intinf_add (BFRelaxFinite x) BFRelaxInfinite =
     BFRelaxInfinite) /\
  (bf_relax_intinf_add (BFRelaxFinite x) (BFRelaxFinite y) =
     BFRelaxFinite (x + y))`;

val bf_relax_intinf_lt_def = Define `
  (bf_relax_intinf_lt BFRelaxInfinite y = F) /\
  (bf_relax_intinf_lt (BFRelaxFinite x) BFRelaxInfinite = T) /\
  (bf_relax_intinf_lt (BFRelaxFinite x) (BFRelaxFinite y) <=> x < y)`;

val bf_relax_path_def = Define `
  (bf_relax_path edge x [] z <=> x = z) /\
  (bf_relax_path edge x (h::t) z <=>
     h = x /\ ?y. edge x y /\ bf_relax_path edge y t z)`;

val bf_relax_path_weight_def = Define `
  (bf_relax_path_weight weight [] dst = (0 : int)) /\
  (bf_relax_path_weight weight (x::xs) dst =
     if xs = [] then weight x dst
     else
       weight x (HD xs) +
       bf_relax_path_weight weight xs dst)`;

val bf_relax_inv1_def = Define `
  bf_relax_inv1 vertices edge source weight lookup m pass via <=>
    !v.
      v IN vertices ==>
      case lookup m v of
        BFRelaxFinite n =>
          (?l.
             bf_relax_path edge source l v /\
             bf_relax_path_weight weight l v = n) /\
          (!l.
             bf_relax_path edge source l v ==>
             &(LENGTH l) < pass ==>
             n <= bf_relax_path_weight weight l v) /\
          (!u l.
             bf_relax_path edge source l u ==>
             &(LENGTH l) < pass ==>
             (u,v) IN via ==>
             n <=
               bf_relax_path_weight weight l u +
               weight u v)
      | BFRelaxInfinite =>
          (!l.
             bf_relax_path edge source l v ==>
             pass <= &(LENGTH l)) /\
          (!u.
             (u,v) IN via ==>
             !lu.
               bf_relax_path edge source lu u ==>
               pass <= &(LENGTH lu))`;

val bellman_ford_relax_vc =
  ``!(vertices : 'vertex set)
      (edges : ('vertex # 'vertex) set)
      (source : 'vertex)
      (weight : 'vertex -> 'vertex -> int)
      (contents : 'distmap -> 'vertex -> bf_relax_intinf)
      (lookup : 'distmap -> 'vertex -> bf_relax_intinf)
      (update :
         'distmap -> 'vertex -> bf_relax_intinf -> 'distmap)
      (pass : int)
      (u : 'vertex)
      (v : 'vertex)
      (via : ('vertex # 'vertex) set)
      (m : 'distmap).
      FINITE vertices /\
      FINITE edges /\
      FINITE via /\
      (!x y.
         (x,y) IN edges ==>
         x IN vertices /\ y IN vertices) /\
      source IN vertices /\
      (!m1 k. lookup m1 k = contents m1 k) /\
      (!m1 k x q.
         contents (update m1 k x) q =
         if q = k then x else contents m1 q) ==>
      let edge = \x y. (x,y) IN edges in
        (1 : int) <= pass /\
        edge u v /\
        ~((u,v) IN via) /\
        bf_relax_inv1
          vertices edge source weight lookup m pass via ==>
        let o1 = lookup m u in
          o1 = contents m u ==>
          let n =
            bf_relax_intinf_add o1
              (BFRelaxFinite (weight u v))
          in
          let o2 = lookup m v in
            o2 = contents m v ==>
            if bf_relax_intinf_lt n o2 then
              bf_relax_inv1
                vertices edge source weight lookup
                (update m v n) pass ((u,v) INSERT via)
            else
              bf_relax_inv1
                vertices edge source weight lookup
                m pass ((u,v) INSERT via)``;
