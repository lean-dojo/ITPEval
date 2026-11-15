(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bellman_ford_BellmanFord_bellman_fordqtvc: a Bellman-Ford
  verification condition expressing the pass invariants, edge-relaxation
  invariant, negative-cycle outcome, and final shortest-path distances over a
  finite weighted directed graph. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory pred_setTheory;

Datatype:
  bf_intinf = BFFinite int | BFInfinite
End

val bf_intinf_add_def = Define `
  (bf_intinf_add BFInfinite y = BFInfinite) /\
  (bf_intinf_add (BFFinite x) BFInfinite = BFInfinite) /\
  (bf_intinf_add (BFFinite x) (BFFinite y) = BFFinite (x + y))`;

val bf_intinf_lt_def = Define `
  (bf_intinf_lt BFInfinite y = F) /\
  (bf_intinf_lt (BFFinite x) BFInfinite = T) /\
  (bf_intinf_lt (BFFinite x) (BFFinite y) <=> x < y)`;

val bf_intinf_le_def = Define `
  bf_intinf_le x y <=> bf_intinf_lt x y \/ x = y`;

val bf_path_def = Define `
  (bf_path edge x [] z <=> x = z) /\
  (bf_path edge x (h::t) z <=>
     h = x /\ ?y. edge x y /\ bf_path edge y t z)`;

val bf_path_weight_def = Define `
  (bf_path_weight weight [] dst = (0 : int)) /\
  (bf_path_weight weight (x::xs) dst =
     if xs = [] then weight x dst
     else weight x (HD xs) + bf_path_weight weight xs dst)`;

val bf_negative_cycle_def = Define `
  bf_negative_cycle vertices edge source weight v <=>
    v IN vertices /\
    (?l1. bf_path edge source l1 v) /\
    ?l2.
      bf_path edge v l2 v /\
      bf_path_weight weight l2 v < (0 : int)`;

val bf_inv1_def = Define `
  bf_inv1 vertices edge source weight lookup m pass via <=>
    !v.
      v IN vertices ==>
      case lookup m v of
        BFFinite n =>
          (?l.
             bf_path edge source l v /\
             bf_path_weight weight l v = n) /\
          (!l.
             bf_path edge source l v ==>
             &(LENGTH l) < pass ==>
             n <= bf_path_weight weight l v) /\
          (!u l.
             bf_path edge source l u ==>
             &(LENGTH l) < pass ==>
             (u,v) IN via ==>
             n <= bf_path_weight weight l u + weight u v)
      | BFInfinite =>
          (!l.
             bf_path edge source l v ==>
             pass <= &(LENGTH l)) /\
          (!u.
             (u,v) IN via ==>
             !lu.
               bf_path edge source lu u ==>
               pass <= &(LENGTH lu))`;

val bf_inv2_def = Define `
  bf_inv2 edge weight lookup m via <=>
    !u v.
      (u,v) IN via ==>
      bf_intinf_le
        (lookup m v)
        (bf_intinf_add (lookup m u) (BFFinite (weight u v)))`;

val bf_final_distances_def = Define `
  bf_final_distances vertices edge source weight lookup m <=>
    !v.
      v IN vertices ==>
      case lookup m v of
        BFFinite n =>
          (?l.
             bf_path edge source l v /\
             bf_path_weight weight l v = n) /\
          !l.
            bf_path edge source l v ==>
            n <= bf_path_weight weight l v
      | BFInfinite =>
          !l. ~bf_path edge source l v`;

val bf_pass_phase_def = Define `
  bf_pass_phase
    vertices edges edge source weight to_fset choose lookup m1 i <=>
    !es.
      to_fset es = edges ==>
      (to_fset es SUBSET edges /\
       bf_inv1 vertices edge source weight lookup m1 i
         (edges DIFF to_fset es)) /\
      !es1 m2.
        to_fset es1 SUBSET edges /\
        bf_inv1 vertices edge source weight lookup m2 i
          (edges DIFF to_fset es1) ==>
        if to_fset es1 <> {} then
          let via = edges DIFF to_fset es1 in
            to_fset es1 <> {} /\
            !es2.
              let o2 = choose es1 in
                o2 IN to_fset es1 /\
                to_fset es2 = to_fset es1 DELETE o2 ==>
                case o2 of
                  (u,v) =>
                    ((1 <= i /\
                      (u,v) IN edges /\
                      ~((u,v) IN via)) /\
                     bf_inv1 vertices edge source weight lookup m2 i via) /\
                    !m3.
                      bf_inv1 vertices edge source weight lookup m3 i
                        ((u,v) INSERT via) ==>
                      ((0 : int) <= &(CARD (to_fset es1)) /\
                       CARD (to_fset es2) < CARD (to_fset es1)) /\
                      to_fset es2 SUBSET edges /\
                      bf_inv1 vertices edge source weight lookup m3 i
                        (edges DIFF to_fset es2)
        else
          bf_inv1 vertices edge source weight lookup m2 (i + 1) {}`;

val bf_relax_phase_def = Define `
  bf_relax_phase
    vertices edges edge source weight to_fset choose contents lookup m <=>
    !es.
      to_fset es = edges ==>
      (to_fset es SUBSET edges /\
       bf_inv2 edge weight lookup m (edges DIFF to_fset es)) /\
      !es1.
        to_fset es1 SUBSET edges /\
        bf_inv2 edge weight lookup m (edges DIFF to_fset es1) ==>
        if to_fset es1 <> {} then
          to_fset es1 <> {} /\
          !es2.
            let o2 = choose es1 in
              o2 IN to_fset es1 /\
              to_fset es2 = to_fset es1 DELETE o2 ==>
              case o2 of
                (u,v) =>
                  let o3 = lookup m v in
                    o3 = contents m v ==>
                    let o4 = lookup m u in
                      o4 = contents m u ==>
                      if bf_intinf_lt
                           (bf_intinf_add o4 (BFFinite (weight u v))) o3
                      then
                        ?v1.
                          bf_negative_cycle
                            vertices edge source weight v1
                      else
                        ((0 : int) <= &(CARD (to_fset es1)) /\
                         CARD (to_fset es2) < CARD (to_fset es1)) /\
                        to_fset es2 SUBSET edges /\
                        bf_inv2 edge weight lookup m
                          (edges DIFF to_fset es2)
        else
          bf_final_distances vertices edge source weight lookup m`;

val bellman_ford_vc =
  ``!(vertices : 'vertex set)
      (edges : ('vertex # 'vertex) set)
      (source : 'vertex)
      (weight : 'vertex -> 'vertex -> int)
      (to_fset : 'edge_collection -> ('vertex # 'vertex) set)
      (choose : 'edge_collection -> 'vertex # 'vertex)
      (contents : 'distmap -> 'vertex -> bf_intinf)
      (create : bf_intinf -> 'distmap)
      (lookup : 'distmap -> 'vertex -> bf_intinf)
      (update : 'distmap -> 'vertex -> bf_intinf -> 'distmap).
      FINITE vertices /\
      FINITE edges /\
      (!es. FINITE (to_fset es)) /\
      (!u v.
         (u,v) IN edges ==>
         u IN vertices /\ v IN vertices) /\
      source IN vertices /\
      (!es.
         to_fset es <> {} ==>
         choose es IN to_fset es) /\
      (!x v. contents (create x) v = x) /\
      (!m k. lookup m k = contents m k) /\
      (!m k x q.
         contents (update m k x) q =
         if q = k then x else contents m q) ==>
      let edge = \u v. (u,v) IN edges in
      let m = update (create BFInfinite) source (BFFinite 0) in
      let o1 = &(CARD vertices) - (1 : int) in
        ((1 : int) <= o1 + 1 ==>
         bf_inv1 vertices edge source weight lookup m 1 {} /\
         !m1.
           (!i.
              ((1 : int) <= i /\ i <= o1) /\
              bf_inv1 vertices edge source weight lookup m1 i {} ==>
              bf_pass_phase
                vertices edges edge source weight
                to_fset choose lookup m1 i) /\
           (bf_inv1 vertices edge source weight lookup m1 (o1 + 1) {} ==>
            bf_relax_phase
              vertices edges edge source weight
              to_fset choose contents lookup m1)) /\
        (o1 + 1 < (1 : int) ==>
         bf_relax_phase
           vertices edges edge source weight
           to_fset choose contents lookup m)``;
