(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/search_Bfs_bfsqtvc: the breadth-first search verification condition
  over abstract states, finite successor sequences, path lengths, frontier
  invariants, and successful-state minimality. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val (search_bfs_path_rules,
     search_bfs_path_ind,
     search_bfs_path_cases) =
  Hol_reln `
    (!moves s.
       search_bfs_path moves s s (0 : int)) /\
    (!moves s i.
       (0 : int) <= i /\
       i < &(LENGTH (moves s)) ==>
       search_bfs_path
         moves s (EL (Num i) (moves s)) (1 : int)) /\
    (!moves s t n u m.
       search_bfs_path moves s t n /\
       search_bfs_path moves t u m ==>
       search_bfs_path moves s u (n + m))
  `;

val search_bfs_move_def = Define `
  search_bfs_move moves s t <=>
    ?i : int.
      (0 : int) <= i /\
      i < &(LENGTH (moves s)) /\
      t = EL (Num i) (moves s)`;

val search_bfs_get_def = Define `
  search_bfs_get (xs : 'a list) (i : int) =
    EL (Num i) xs`;

val search_bfs_level_inv_def = Define `
  search_bfs_level_inv moves start success p cur <=>
    (0 : int) <= p /\
    (!i : int.
       (0 : int) <= i /\
       i < &(LENGTH cur) ==>
       search_bfs_path moves start (search_bfs_get cur i) p) /\
    (!t.
       search_bfs_path moves start t p ==>
       MEM t cur) /\
    (!t n.
       search_bfs_path moves start t n ==>
       success t ==>
       p <= n)`;

val search_bfs_inner_inv_def = Define `
  search_bfs_inner_inv moves success cur i nxt <=>
    (!l : int.
       (0 : int) <= l /\
       l < &(LENGTH nxt) ==>
       ?j : int.
         ((0 : int) <= j /\ j < i) /\
         search_bfs_move
           moves (search_bfs_get cur j) (search_bfs_get nxt l)) /\
    (!j k : int.
       (0 : int) <= j /\ j < i ==>
       (0 : int) <= k /\
       k < &(LENGTH (moves (search_bfs_get cur j))) ==>
       MEM
         (search_bfs_get
            (moves (search_bfs_get cur j)) k)
         nxt) /\
    (!j : int.
       (0 : int) <= j /\ j < i ==>
       ~success (search_bfs_get cur j))`;

val search_bfs_cons_spec_def = Define `
  search_bfs_cons_spec o2 o1 o3 <=>
    &(LENGTH o3) = (1 : int) + &(LENGTH o1) /\
    search_bfs_get o3 (0 : int) = o2 /\
    (!i : int.
       (0 : int) < i /\
       i <= &(LENGTH o1) ==>
       search_bfs_get o3 i =
         search_bfs_get o1 (i - (1 : int)))`;

val search_bfs_append_spec_def = Define `
  search_bfs_append_spec o5 nxt o6 <=>
    &(LENGTH o6) = &(LENGTH o5) + &(LENGTH nxt) /\
    (!i : int.
       (0 : int) <= i /\
       i < &(LENGTH o5) ==>
       search_bfs_get o6 i = search_bfs_get o5 i) /\
    (!i : int.
       &(LENGTH o5) <= i /\
       i < &(LENGTH o6) ==>
       search_bfs_get o6 i =
         search_bfs_get nxt (i - &(LENGTH o5)))`;

val search_Bfs_bfsqtvc =
  ``!(moves : 'state -> 'state list)
      (start : 'state)
      (success : 'state -> bool).
      let o1 = ([] : 'state list)
      in
      let o2 = start
      in
      let o3 = o2::o1
      in
        search_bfs_cons_spec o2 o1 o3 ==>
        search_bfs_level_inv
          moves start success (0 : int) o3 /\
        !p : int.
        !cur : 'state list.
          search_bfs_level_inv moves start success p cur ==>
          if (0 : int) < &(LENGTH cur) then
            let o4 = &(LENGTH cur) - (1 : int)
            in
              (((0 : int) <= o4 + (1 : int) ==>
                 search_bfs_inner_inv
                   moves success cur (0 : int) ([] : 'state list) /\
                 !nxt : 'state list.
                   ((!i : int.
                       (((0 : int) <= i /\ i <= o4) /\
                        search_bfs_inner_inv
                          moves success cur i nxt) ==>
                       let s = search_bfs_get cur i
                       in
                         if success s then
                           search_bfs_path moves start s p
                         else
                           let o5 = moves s
                           in
                           let o6 = o5 ++ nxt
                           in
                             search_bfs_append_spec o5 nxt o6 ==>
                             search_bfs_inner_inv
                               moves success cur
                               (i + (1 : int)) o6) /\
                    (search_bfs_inner_inv
                       moves success cur
                       (o4 + (1 : int)) nxt ==>
                     search_bfs_level_inv
                       moves start success
                       (p + (1 : int)) nxt))) /\
               (o4 + (1 : int) < (0 : int) ==>
                search_bfs_level_inv
                  moves start success
                  (p + (1 : int)) ([] : 'state list)))
          else
            !t : 'state.
            !n : int.
              success t ==>
              ~search_bfs_path moves start t n``;
