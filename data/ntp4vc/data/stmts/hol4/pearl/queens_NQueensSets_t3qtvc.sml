(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/queens_NQueensSets_t3qtvc: the finite integer-set N-queens
  verification condition for enumerating and sorting all completions of a
  partial solution while preserving the recursive loop invariants. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory pred_setTheory;

val queens_t3_min_def = Define `
  queens_t3_min (e : int set) =
    @d : int.
      d IN e /\
      !x : int. x IN e ==> d <= x`;

val queens_t3_update_def = Define `
  queens_t3_update (f : 'a -> 'b) (k : 'a) (v : 'b) =
    \x. if x = k then v else f x`;

val queens_t3_eq_prefix_def = Define `
  queens_t3_eq_prefix
    (t : int -> 'a) (u : int -> 'a) (i : int) <=>
      !k : int.
        0 <= k /\ k < i ==>
        t k = u k`;

val queens_t3_partial_solution_def = Define `
  queens_t3_partial_solution
    (n : int) (k : int) (s : int -> int) <=>
      !i : int.
        0 <= i /\ i < k ==>
        (0 <= s i /\ s i < n) /\
        !j : int.
          0 <= j /\ j < i ==>
          s i <> s j /\
          s i - s j <> i - j /\
          s i - s j <> j - i`;

val queens_t3_lt_sol_def = Define `
  queens_t3_lt_sol
    (n : int) (s1 : int -> int) (s2 : int -> int) <=>
      ?i : int.
        (0 <= i /\ i < n) /\
        queens_t3_eq_prefix s1 s2 i /\
        s1 i < s2 i`;

val queens_t3_sorted_def = Define `
  queens_t3_sorted
    (n : int) (sol : int -> int -> int) (a : int) (b : int) <=>
      !i : int. !j : int.
        a <= i /\ i < j /\ j < b ==>
        queens_t3_lt_sol n (sol i) (sol j)`;

val queens_t3_pre_def = Define `
  queens_t3_pre
    (n : int)
    (k : int)
    (a : int set)
    (s : int)
    (col : int -> int)
    (b : int set)
    (c : int set) <=>
      FINITE a /\
      FINITE b /\
      FINITE c /\
      0 <= k /\
      k + &(CARD a) = n /\
      0 <= s /\
      (!i : int.
         i IN a <=>
         (0 <= i /\ i < n) /\
         (!j : int.
            0 <= j /\ j < k ==>
            col j <> i)) /\
      (!i : int.
         0 <= i ==>
         (~(i IN b) <=>
          !j : int.
            0 <= j /\ j < k ==>
            col j <> i + j - k)) /\
      (!i : int.
         0 <= i ==>
         (~(i IN c) <=>
          !j : int.
            0 <= j /\ j < k ==>
            col j <> i + k - j)) /\
      queens_t3_partial_solution n k col`;

val queens_t3_loop_inv_def = Define `
  queens_t3_loop_inv
    (n : int)
    (k : int)
    (a : int set)
    (b : int set)
    (c : int set)
    (s : int)
    (col : int -> int)
    (sol : int -> int -> int)
    (o2 : int set)
    (e : int set)
    (s1 : int)
    (sol1 : int -> int -> int)
    (col1 : int -> int) <=>
      (0 <= s1 - s /\
       e SUBSET ((a DIFF b) DIFF c) /\
       queens_t3_partial_solution n k col1 /\
       queens_t3_sorted n sol1 s s1 /\
       (!i : int. !j : int.
          i IN (o2 DIFF e) ==>
          j IN e ==>
          i < j)) /\
      (!i : int.
         s <= i /\ i < s1 ==>
         queens_t3_partial_solution n n (sol1 i) /\
         queens_t3_eq_prefix col1 (sol1 i) k /\
         sol1 i k IN (o2 DIFF e)) /\
      (!t : int -> int.
         queens_t3_partial_solution n n t /\
         queens_t3_eq_prefix col1 t k /\
         t k IN (o2 DIFF e) ==>
         t k IN o2 /\
         ~(t k IN e) /\
         (?i : int.
            (s <= i /\ i < s1) /\
            queens_t3_eq_prefix t (sol1 i) n)) /\
      queens_t3_eq_prefix col col1 k /\
      queens_t3_eq_prefix sol sol1 s`;

val queens_t3_done_def = Define `
  queens_t3_done
    (n : int)
    (k : int)
    (s : int)
    (col : int -> int)
    (sol : int -> int -> int)
    (s1 : int)
    (col1 : int -> int)
    (sol1 : int -> int -> int) <=>
      0 <= s1 - s /\
      queens_t3_sorted n sol1 s s1 /\
      (!t : int -> int.
         (queens_t3_partial_solution n n t /\
          queens_t3_eq_prefix col1 t k) <=>
         ?i : int.
           (s <= i /\ i < s1) /\
           queens_t3_eq_prefix t (sol1 i) n) /\
      queens_t3_eq_prefix col col1 k /\
      queens_t3_eq_prefix sol sol1 s`;

val queens_NQueensSets_t3_vc =
  ``!n : int.
    !k : int.
    !a : int set.
    !s : int.
    !col : int -> int.
    !b : int set.
    !c : int set.
    !sol : int -> int -> int.
      queens_t3_pre n k a s col b c ==>
      if a <> {} then
        !o1 : int set.
          FINITE o1 ==>
          o1 = a DIFF b ==>
          !o2 : int set.
            FINITE o2 ==>
            o2 = o1 DIFF c ==>
            (0 : int) = s - s /\
            queens_t3_loop_inv
              n k a b c s col sol o2 o2 s sol col /\
            !e : int set.
            !s1 : int.
            !sol1 : int -> int -> int.
            !col1 : int -> int.
              FINITE e ==>
              queens_t3_loop_inv
                n k a b c s col sol o2 e s1 sol1 col1 ==>
              if e <> {} then
                e <> {} /\
                let d = queens_t3_min e
                in
                  !o3 : int set.
                    FINITE o3 ==>
                    o3 = d INSERT c /\
                    (if d IN c then
                       CARD o3 = CARD c
                     else
                       &(CARD o3) = &(CARD c) + (1 : int))
                    ==>
                    !o4 : int set.
                      FINITE o4 ==>
                      (!i : int.
                         i IN o4 <=>
                         0 <= i /\ i + (1 : int) IN o3)
                      ==>
                      !o5 : int set.
                        FINITE o5 ==>
                        o5 = d INSERT b /\
                        (if d IN b then
                           CARD o5 = CARD b
                         else
                           &(CARD o5) = &(CARD b) + (1 : int))
                        ==>
                        !o6 : int set.
                          FINITE o6 ==>
                          (!i : int.
                             i IN o6 <=>
                             (1 : int) <= i /\
                             i - (1 : int) IN o5)
                          ==>
                          !o7 : int set.
                            FINITE o7 ==>
                            o7 = a DELETE d /\
                            (if d IN a then
                               &(CARD o7) =
                                 &(CARD a) - (1 : int)
                             else
                               CARD o7 = CARD a)
                            ==>
                            ((0 : int) <= &(CARD a) /\
                             &(CARD o7) < &(CARD a)) /\
                            queens_t3_pre
                              n
                              (k + (1 : int))
                              o7
                              s1
                              (queens_t3_update col1 k d)
                              o6
                              o4 /\
                            !s2 : int.
                            !sol2 : int -> int -> int.
                            !col2 : int -> int.
                              queens_t3_done
                                n
                                (k + (1 : int))
                                s1
                                (queens_t3_update col1 k d)
                                sol1
                                s2
                                col2
                                sol2
                              ==>
                              !o8 : int set.
                                FINITE o8 ==>
                                o8 = e DELETE d /\
                                (if d IN e then
                                   &(CARD o8) =
                                     &(CARD e) - (1 : int)
                                 else
                                   CARD o8 = CARD e)
                                ==>
                                ((0 : int) <= &(CARD e) /\
                                 &(CARD o8) < &(CARD e)) /\
                                s1 - s + (s2 - s1) = s2 - s /\
                                k + (1 : int) - (1 : int) = k /\
                                queens_t3_loop_inv
                                  n
                                  (k + (1 : int) - (1 : int))
                                  a
                                  b
                                  c
                                  s
                                  col
                                  sol
                                  o2
                                  o8
                                  s2
                                  sol2
                                  col2
              else
                queens_t3_done
                  n k s col sol s1 col1 sol1
      else
        (1 : int) = s + (1 : int) - s /\
        queens_t3_done
          n
          k
          s
          col
          sol
          (s + (1 : int))
          col
          (queens_t3_update sol s col)``;
