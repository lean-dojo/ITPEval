(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/search_Dfs_dfsqtvc: the depth-first-search verification condition
  for bounded successful paths and preservation of the recursive child-search
  loop invariant. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val (search_dfs_path_rules,
     search_dfs_path_ind,
     search_dfs_path_cases) =
  Hol_reln `
    (!moves s.
       search_dfs_path moves s s (0 : int)) /\
    (!moves s i.
       (0 : int) <= i /\
       i < &(LENGTH (moves s)) ==>
       search_dfs_path
         moves s (EL (Num i) (moves s)) (1 : int)) /\
    (!moves s t n u m.
       search_dfs_path moves s t n /\
       search_dfs_path moves t u m ==>
       search_dfs_path moves s u (n + m))
  `;

val search_dfs_get_def = Define `
  search_dfs_get (xs : 'a list) (i : int) =
    EL (Num i) xs`;

val search_Dfs_dfsqtvc =
  ``!(moves : 'state -> 'state list)
      (success : 'state -> bool)
      (p : int) (m : int) (s : 'state).
      (0 : int) <= p /\
      p <= m + (1 : int)
      ==>
      if m < p then
        !t : 'state.
        !n : int.
          (0 : int) <= n /\
          n <= m - p ==>
          success t ==>
          ~search_dfs_path moves s t n
      else if success s then
        search_dfs_path moves s s (0 : int) /\
        success s /\
        (0 : int) <= (0 : int) /\
        (0 : int) <= m - p
      else
        let mv = moves s
        in
        let o1 = &(LENGTH mv) - (1 : int)
        in
          ((0 : int) <= o1 + (1 : int) ==>
           (!j : int.
            !t : 'state.
            !n : int.
              (0 : int) <= j /\
              j < (0 : int) ==>
              search_dfs_path
                moves (search_dfs_get mv j) t n ==>
              success t ==>
              ~((0 : int) <= n /\ n < m - p)) /\
           (!i : int.
              (((0 : int) <= i /\ i <= o1) /\
               (!j : int.
                !t : 'state.
                !n : int.
                  (0 : int) <= j /\
                  j < i ==>
                  search_dfs_path
                    moves (search_dfs_get mv j) t n ==>
                  success t ==>
                  ~((0 : int) <= n /\ n < m - p)))
              ==>
              let o2 = p + (1 : int)
              in
              let o3 = search_dfs_get mv i
              in
                (((0 : int) <= m - p /\
                  m - o2 < m - p) /\
                 (0 : int) <= o2 /\
                 o2 <= m + (1 : int)) /\
                (!o4 : ('state # int) option.
                   (case o4 of
                      NONE =>
                        !t : 'state.
                        !n : int.
                          (0 : int) <= n /\
                          n <= m - o2 ==>
                          success t ==>
                          ~search_dfs_path moves o3 t n
                    | SOME (t,n) =>
                        search_dfs_path moves o3 t n /\
                        success t /\
                        (0 : int) <= n /\
                        n <= m - o2)
                   ==>
                   (case o4 of
                      SOME (t,n) =>
                        let o5 = n + (1 : int)
                        in
                          search_dfs_path moves s t o5 /\
                          success t /\
                          (0 : int) <= o5 /\
                          o5 <= m - p
                    | NONE =>
                        !j : int.
                        !t : 'state.
                        !n : int.
                          (0 : int) <= j /\
                          j < i + (1 : int) ==>
                          search_dfs_path
                            moves (search_dfs_get mv j) t n ==>
                          success t ==>
                          ~((0 : int) <= n /\ n < m - p))))) /\
          (((!j : int.
             !t : 'state.
             !n : int.
               (0 : int) <= j /\
               j < o1 + (1 : int) ==>
               search_dfs_path
                 moves (search_dfs_get mv j) t n ==>
               success t ==>
               ~((0 : int) <= n /\ n < m - p))
            ==>
            (!t : 'state.
             !n : int.
               (0 : int) <= n /\
               n <= m - p ==>
               success t ==>
               ~search_dfs_path moves s t n))) /\
          (o1 + (1 : int) < (0 : int) ==>
           (!t : 'state.
            !n : int.
              (0 : int) <= n /\
              n <= m - p ==>
              success t ==>
              ~search_dfs_path moves s t n))``;
