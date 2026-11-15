(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linked_list_rev_Termination_list_reversalqtvc: the termination
  verification condition for in-place linked-list reversal, using finite
  memory closure, integer visit ranks, and lexicographic descent across a
  next-pointer update. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val llrev_valid_cells_def = Define `
  llrev_valid_cells
    (null : 'loc)
    (s : int -> 'loc)
    (n : int) <=>
      (!i : int.
         (0 : int) <= i /\ i < n ==>
         ~(s i = null)) /\
      (!i j : int.
         (0 : int) <= i /\ i < n ==>
         (0 : int) <= j /\ j < n ==>
         ~(i = j) ==>
         ~(s i = s j))`;

val llrev_inside_memory_def = Define `
  llrev_inside_memory
    (null : 'loc)
    (s : int -> 'loc)
    (n : int)
    (l : 'loc) <=>
      l = null \/
      ?i : int.
        ((0 : int) <= i /\ i < n) /\
        l = s i`;

val llrev_finite_memory_def = Define `
  llrev_finite_memory
    (null : 'loc)
    (next : 'loc -> 'loc)
    (s : int -> 'loc)
    (n : int) <=>
      !i : int.
        (0 : int) <= i /\ i < n ==>
        llrev_inside_memory null s n (next (s i))`;

val llrev_fun_update_def = Define `
  llrev_fun_update (f : 'a -> 'b) (k : 'a) (v : 'b) =
    \x. if x = k then v else f x`;

val llrev_seen_def = Define `
  llrev_seen
    (s : int -> 'loc)
    (idx : 'loc -> int)
    (lo : int)
    (hi : int) =
      (&(LENGTH
          (FILTER
            (\i. (0 : int) < idx (s i))
            (GENLIST (\k. lo + &k) (Num (hi - lo))))) : int)`;

val llrev_initial_rank_def = Define `
  llrev_initial_rank (null : 'loc) (p : 'loc) =
    if p = null then (0 : int) else -(1 : int)`;

val linked_list_rev_Termination_list_reversal_vc =
  ``!(null : 'loc)
      (mem1 : 'loc -> 'loc)
      (s : int -> 'loc)
      (n : int)
      (l : 'loc).
      (0 : int) <= n /\
      llrev_valid_cells null s n /\
      llrev_finite_memory null mem1 s n /\
      llrev_inside_memory null s n l ==>
      let o2 = llrev_initial_rank null
      in
        llrev_inside_memory null s n l /\
        llrev_inside_memory null s n null /\
        llrev_finite_memory null mem1 s n /\
        ((0 : int) = llrev_seen s o2 (0 : int) n /\
         (0 : int) <= llrev_seen s o2 (0 : int) n) /\
        (!i : int.
           (0 : int) <= i /\ i < n ==>
           -(1 : int) <= o2 (s i) /\
           o2 (s i) <= (0 : int)) /\
        (!p : 'loc.
           (o2 p = (0 : int) <=> p = null)) /\
        (if o2 l = -(1 : int) then
           o2 null = (0 : int) /\
           (!i : int.
              (0 : int) <= i /\ i < n ==>
              (0 : int) < o2 (s i) ==>
              o2 (mem1 (s i)) = o2 (s i) - (1 : int))
         else
           !i : int.
             (0 : int) <= i /\ i < n ==>
             (0 : int) < o2 (s i) /\
             o2 (s i) <= o2 l ==>
             o2 (mem1 (s i)) = o2 (s i) - (1 : int)) /\
        (!idx : 'loc -> int.
         !r : 'loc.
         !l1 : 'loc.
         !mem3 : 'loc -> 'loc.
           let k = llrev_seen s idx (0 : int) n
           in
             llrev_inside_memory null s n l1 /\
             llrev_inside_memory null s n r /\
             llrev_finite_memory null mem3 s n /\
             (0 : int) <= k /\
             (!i : int.
                (0 : int) <= i /\ i < n ==>
                -(1 : int) <= idx (s i) /\
                idx (s i) <= k) /\
             (!p : 'loc.
                (idx p = (0 : int) <=> p = null)) /\
             (if idx l1 = -(1 : int) then
                idx r = k /\
                (!i : int.
                   (0 : int) <= i /\ i < n ==>
                   (0 : int) < idx (s i) ==>
                   idx (mem3 (s i)) =
                     idx (s i) - (1 : int))
              else
                !i : int.
                  (0 : int) <= i /\ i < n ==>
                  (0 : int) < idx (s i) /\
                  idx (s i) <= idx l1 ==>
                  idx (mem3 (s i)) =
                    idx (s i) - (1 : int)) ==>
             ~(l1 = null) ==>
             let idx1 =
               llrev_fun_update idx l1 (k + (1 : int))
             in
             let mem4 = llrev_fun_update mem3 l1 r
             in
               if idx l1 = -(1 : int) then
                 (llrev_valid_cells null s n /\
                  llrev_inside_memory null s n l1 /\
                  ~(l1 = null) /\
                  idx l1 = -(1 : int) /\
                  (0 : int) <= k) /\
                 (llrev_seen s idx1 (0 : int) n =
                    (1 : int) + k ==>
                  ~(l1 = null) /\
                  ~(l1 = null) /\
                  (((0 : int) <= n - k /\
                    n - (k + (1 : int)) < n - k) \/
                   (n - k = n - (k + (1 : int)) /\
                    (0 : int) <= (1 : int) + idx l1 /\
                    (1 : int) + idx1 (mem3 l1) <
                      (1 : int) + idx l1)) /\
                  llrev_inside_memory null s n (mem3 l1) /\
                  llrev_inside_memory null s n l1 /\
                  llrev_finite_memory null mem4 s n /\
                  (k + (1 : int) =
                     llrev_seen s idx1 (0 : int) n /\
                   (0 : int) <=
                     llrev_seen s idx1 (0 : int) n) /\
                  (!i : int.
                     (0 : int) <= i /\ i < n ==>
                     -(1 : int) <= idx1 (s i) /\
                     idx1 (s i) <= k + (1 : int)) /\
                  (!p : 'loc.
                     (idx1 p = (0 : int) <=> p = null)) /\
                  (if idx1 (mem3 l1) = -(1 : int) then
                     idx1 l1 = k + (1 : int) /\
                     (!i : int.
                        (0 : int) <= i /\ i < n ==>
                        (0 : int) < idx1 (s i) ==>
                        idx1 (mem4 (s i)) =
                          idx1 (s i) - (1 : int))
                   else
                     !i : int.
                       (0 : int) <= i /\ i < n ==>
                       (0 : int) < idx1 (s i) /\
                       idx1 (s i) <= idx1 (mem3 l1) ==>
                       idx1 (mem4 (s i)) =
                         idx1 (s i) - (1 : int)))
               else
                 ~(l1 = null) /\
                 ~(l1 = null) /\
                 (((0 : int) <= n - k /\
                   n - k < n - k) \/
                  ((0 : int) <= (1 : int) + idx l1 /\
                   (1 : int) + idx (mem3 l1) <
                     (1 : int) + idx l1)) /\
                 llrev_inside_memory null s n (mem3 l1) /\
                 llrev_inside_memory null s n l1 /\
                 llrev_finite_memory null mem4 s n /\
                 (0 : int) <= k /\
                 (!i : int.
                    (0 : int) <= i /\ i < n ==>
                    -(1 : int) <= idx (s i) /\
                    idx (s i) <= k) /\
                 (!p : 'loc.
                    (idx p = (0 : int) <=> p = null)) /\
                 (if idx (mem3 l1) = -(1 : int) then
                    idx l1 = k /\
                    (!i : int.
                       (0 : int) <= i /\ i < n ==>
                       (0 : int) < idx (s i) ==>
                       idx (mem4 (s i)) =
                         idx (s i) - (1 : int))
                  else
                    !i : int.
                      (0 : int) <= i /\ i < n ==>
                      (0 : int) < idx (s i) /\
                      idx (s i) <= idx (mem3 l1) ==>
                      idx (mem4 (s i)) =
                        idx (s i) - (1 : int)))``;
