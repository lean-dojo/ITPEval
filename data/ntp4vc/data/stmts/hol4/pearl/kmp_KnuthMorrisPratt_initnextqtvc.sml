(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/kmp_KnuthMorrisPratt_initnextqtvc: the Knuth-Morris-Pratt next-table
  initialization verification condition, preserving substring matching and
  longest proper-prefix invariants across list updates. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val kmp_to_num_def = Define `
  kmp_to_num (z : int) = if z < 0 then 0 else Num z`;

val kmp_get_char_def = Define `
  kmp_get_char (xs : 'a list) (z : int) =
    if kmp_to_num z < LENGTH xs then EL (kmp_to_num z) xs else ARB`;

val kmp_get_int_def = Define `
  kmp_get_int (xs : int list) (z : int) =
    if kmp_to_num z < LENGTH xs then EL (kmp_to_num z) xs else (0 : int)`;

val kmp_matches_def = Define `
  kmp_matches
      (a1 : 'a list) (i1 : int)
      (a2 : 'a list) (i2 : int) (n : int) <=>
    ((0 : int) <= i1 /\ i1 <= &(LENGTH a1) - n) /\
    ((0 : int) <= i2 /\ i2 <= &(LENGTH a2) - n) /\
    !i : int.
      (0 : int) <= i /\ i < n ==>
      kmp_get_char a1 (i1 + i) = kmp_get_char a2 (i2 + i)`;

val kmp_is_next_def = Define `
  kmp_is_next (p : 'a list) (j : int) (n : int) <=>
    ((0 : int) <= n /\ n < j) /\
    kmp_matches p (j - n) p (0 : int) n /\
    !z : int.
      n < z /\ z < j ==>
      ~kmp_matches p (j - z) p (0 : int) z`;

val kmp_KnuthMorrisPratt_initnext_vc =
  ``!p : 'a list.
      (1 : int) <= &(LENGTH p) ==>
      let m = &(LENGTH p) in
        (0 : int) <= m /\
        !next : int list.
          ((!i : int.
              (0 : int) <= i /\ i < m ==>
              kmp_get_int next i = (0 : int)) /\
           &(LENGTH next) = m)
          ==>
          if (1 : int) < m then
            ((0 : int) <= (1 : int) /\
             (1 : int) < &(LENGTH next)) /\
            (LENGTH (LUPDATE (0 : int) 1 next) = LENGTH next ==>
             (\z : int. kmp_get_int (LUPDATE (0 : int) 1 next) z) =
               (\z : int.
                  if z = (1 : int) then
                    (0 : int)
                  else
                    kmp_get_int next z)
             ==>
             ((((0 : int) <= (0 : int) /\
                (0 : int) < (1 : int) /\
                (1 : int) <= m) /\
               kmp_matches
                 p ((1 : int) - (0 : int)) p (0 : int) (0 : int) /\
               (!z : int.
                  (0 : int) + (1 : int) < z /\
                  z < (1 : int) + (1 : int)
                  ==>
                  ~kmp_matches
                    p ((1 : int) + (1 : int) - z) p (0 : int) z) /\
               (!k : int.
                  (0 : int) < k /\ k <= (1 : int) ==>
                  kmp_is_next
                    p k (kmp_get_int (LUPDATE (0 : int) 1 next) k))) /\
              (!j i : int.
               !next1 : int list.
                 LENGTH next1 = LENGTH (LUPDATE (0 : int) 1 next) ==>
                 (((0 : int) <= j /\ j < i /\ i <= m) /\
                  kmp_matches p (i - j) p (0 : int) j /\
                  (!z : int.
                     j + (1 : int) < z /\ z < i + (1 : int) ==>
                     ~kmp_matches
                       p (i + (1 : int) - z) p (0 : int) z) /\
                  (!k : int.
                     (0 : int) < k /\ k <= i ==>
                     kmp_is_next p k (kmp_get_int next1 k)))
                 ==>
                 if i < m - (1 : int) then
                   ((0 : int) <= j /\ j < &(LENGTH p)) /\
                   ((0 : int) <= i /\ i < &(LENGTH p)) /\
                   if kmp_get_char p i = kmp_get_char p j then
                     ((0 : int) <= i + (1 : int) /\
                      i + (1 : int) < &(LENGTH next1)) /\
                     (LENGTH
                        (LUPDATE
                           (j + (1 : int))
                           (kmp_to_num (i + (1 : int)))
                           next1) =
                        LENGTH next1
                      ==>
                      (\z : int.
                         kmp_get_int
                           (LUPDATE
                              (j + (1 : int))
                              (kmp_to_num (i + (1 : int)))
                              next1)
                           z) =
                        (\z : int.
                           if z = i + (1 : int) then
                             j + (1 : int)
                           else
                             kmp_get_int next1 z)
                      ==>
                      (((0 : int) <= m - i /\
                         m - (i + (1 : int)) < m - i) \/
                        (m - i = m - (i + (1 : int)) /\
                         (0 : int) <= j /\
                         j + (1 : int) < j)) /\
                      ((0 : int) <= j + (1 : int) /\
                       j + (1 : int) < i + (1 : int) /\
                       i + (1 : int) <= m) /\
                      kmp_matches
                        p (i + (1 : int) - (j + (1 : int)))
                        p (0 : int) (j + (1 : int)) /\
                      (!z : int.
                         j + (1 : int) + (1 : int) < z /\
                         z < i + (1 : int) + (1 : int)
                         ==>
                         ~kmp_matches
                           p (i + (1 : int) + (1 : int) - z)
                           p (0 : int) z) /\
                      (!k : int.
                         (0 : int) < k /\ k <= i + (1 : int) ==>
                         kmp_is_next
                           p k
                           (kmp_get_int
                              (LUPDATE
                                 (j + (1 : int))
                                 (kmp_to_num (i + (1 : int)))
                                 next1)
                              k)))
                   else if j = (0 : int) then
                     ((0 : int) <= i + (1 : int) /\
                      i + (1 : int) < &(LENGTH next1)) /\
                     (LENGTH
                        (LUPDATE
                           (0 : int)
                           (kmp_to_num (i + (1 : int)))
                           next1) =
                        LENGTH next1
                      ==>
                      (\z : int.
                         kmp_get_int
                           (LUPDATE
                              (0 : int)
                              (kmp_to_num (i + (1 : int)))
                              next1)
                           z) =
                        (\z : int.
                           if z = i + (1 : int) then
                             (0 : int)
                           else
                             kmp_get_int next1 z)
                      ==>
                      (((0 : int) <= m - i /\
                         m - (i + (1 : int)) < m - i) \/
                        (m - i = m - (i + (1 : int)) /\
                         (0 : int) <= j /\
                         j < j)) /\
                      ((0 : int) <= j /\
                       j < i + (1 : int) /\
                       i + (1 : int) <= m) /\
                      kmp_matches
                        p (i + (1 : int) - j) p (0 : int) j /\
                      (!z : int.
                         j + (1 : int) < z /\
                         z < i + (1 : int) + (1 : int)
                         ==>
                         ~kmp_matches
                           p (i + (1 : int) + (1 : int) - z)
                           p (0 : int) z) /\
                      (!k : int.
                         (0 : int) < k /\ k <= i + (1 : int) ==>
                         kmp_is_next
                           p k
                           (kmp_get_int
                              (LUPDATE
                                 (0 : int)
                                 (kmp_to_num (i + (1 : int)))
                                 next1)
                              k)))
                   else
                     ((0 : int) <= j /\ j < &(LENGTH next1)) /\
                     (((0 : int) <= m - i /\ m - i < m - i) \/
                      ((0 : int) <= j /\ kmp_get_int next1 j < j)) /\
                     ((0 : int) <= kmp_get_int next1 j /\
                      kmp_get_int next1 j < i /\
                      i <= m) /\
                     kmp_matches
                       p (i - kmp_get_int next1 j)
                       p (0 : int) (kmp_get_int next1 j) /\
                     (!z : int.
                        kmp_get_int next1 j + (1 : int) < z /\
                        z < i + (1 : int)
                        ==>
                        ~kmp_matches
                          p (i + (1 : int) - z) p (0 : int) z) /\
                     (!k : int.
                        (0 : int) < k /\ k <= i ==>
                        kmp_is_next p k (kmp_get_int next1 k))
                 else
                   LENGTH next1 = LENGTH p /\
                   !j1 : int.
                     (0 : int) < j1 /\ j1 < &(LENGTH p) ==>
                     kmp_is_next p j1 (kmp_get_int next1 j1))))
          else
            LENGTH next = LENGTH p /\
            !j : int.
              (0 : int) < j /\ j < &(LENGTH p) ==>
              kmp_is_next p j (kmp_get_int next j)``;
