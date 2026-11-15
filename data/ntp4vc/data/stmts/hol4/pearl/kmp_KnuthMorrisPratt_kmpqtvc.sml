(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/kmp_KnuthMorrisPratt_kmpqtvc: the Knuth-Morris-Pratt search
  verification condition, preserving substring matching, failure-function
  invariants, and the first-occurrence result. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val kmp_search_to_num_def = Define `
  kmp_search_to_num (z : int) =
    if z < 0 then 0 else Num z`;

val kmp_search_get_char_def = Define `
  kmp_search_get_char (xs : 'a list) (z : int) =
    if kmp_search_to_num z < LENGTH xs
    then EL (kmp_search_to_num z) xs
    else ARB`;

val kmp_search_get_int_def = Define `
  kmp_search_get_int (xs : int list) (z : int) =
    if kmp_search_to_num z < LENGTH xs
    then EL (kmp_search_to_num z) xs
    else (0 : int)`;

val kmp_search_matches_def = Define `
  kmp_search_matches
      (a1 : 'a list) (i1 : int)
      (a2 : 'a list) (i2 : int) (n : int) <=>
    ((0 : int) <= i1 /\ i1 <= &(LENGTH a1) - n) /\
    ((0 : int) <= i2 /\ i2 <= &(LENGTH a2) - n) /\
    !i : int.
      (0 : int) <= i /\ i < n ==>
      kmp_search_get_char a1 (i1 + i) =
        kmp_search_get_char a2 (i2 + i)`;

val kmp_search_is_next_def = Define `
  kmp_search_is_next (p : 'a list) (j : int) (n : int) <=>
    ((0 : int) <= n /\ n < j) /\
    kmp_search_matches p (j - n) p (0 : int) n /\
    !z : int.
      n < z /\ z < j ==>
      ~kmp_search_matches p (j - z) p (0 : int) z`;

val kmp_search_first_occur_def = Define `
  kmp_search_first_occur
      (p : 'a list) (a : 'a list) (r : int) <=>
    (((0 : int) <= r /\ r < &(LENGTH a)) ==>
     kmp_search_matches
       a r p (0 : int) (&(LENGTH p))) /\
    !k : int.
      (0 : int) <= k /\ k < r ==>
      ~kmp_search_matches
        a k p (0 : int) (&(LENGTH p))`;

val kmp_KnuthMorrisPratt_kmp_vc =
  ``!p : 'a list. !a : 'a list.
      (1 : int) <= &(LENGTH p) ==>
      let m = &(LENGTH p) in
      let n = &(LENGTH a) in
        (1 : int) <= &(LENGTH p) /\
        !next : int list.
          (LENGTH next = LENGTH p /\
           (!j : int.
              (0 : int) < j /\ j < &(LENGTH p) ==>
              kmp_search_is_next
                p j (kmp_search_get_int next j)))
          ==>
          (((((0 : int) <= (0 : int) /\
              (0 : int) <= m) /\
             (0 : int) <= (0 : int) /\
             (0 : int) <= n) /\
            kmp_search_matches
              a ((0 : int) - (0 : int))
              p (0 : int) (0 : int) /\
            (!k : int.
               (0 : int) <= k /\
               k < (0 : int) - (0 : int) ==>
               ~kmp_search_matches
                 a k p (0 : int) m)) /\
           !j i : int.
             ((((0 : int) <= j /\ j <= m) /\
               j <= i /\ i <= n) /\
              kmp_search_matches
                a (i - j) p (0 : int) j /\
              (!k : int.
                 (0 : int) <= k /\ k < i - j ==>
                 ~kmp_search_matches
                   a k p (0 : int) m))
             ==>
             !o1 : bool.
               (if j < m then
                  o1 = (if i < n then T else F)
                else
                  o1 = F)
               ==>
               if o1 = T then
                 ((0 : int) <= j /\
                  j < &(LENGTH p)) /\
                 ((0 : int) <= i /\
                  i < &(LENGTH a)) /\
                 if kmp_search_get_char a i =
                    kmp_search_get_char p j
                 then
                   (((0 : int) <= n - i /\
                     n - (i + (1 : int)) < n - i) \/
                    (n - i = n - (i + (1 : int)) /\
                     (0 : int) <= j /\
                     j + (1 : int) < j)) /\
                   ((((0 : int) <= j + (1 : int) /\
                      j + (1 : int) <= m) /\
                     j + (1 : int) <= i + (1 : int) /\
                     i + (1 : int) <= n) /\
                    kmp_search_matches
                      a (i + (1 : int) - (j + (1 : int)))
                      p (0 : int) (j + (1 : int)) /\
                    (!k : int.
                       (0 : int) <= k /\
                       k < i + (1 : int) - (j + (1 : int)) ==>
                       ~kmp_search_matches
                         a k p (0 : int) m))
                 else if j = (0 : int) then
                   (((0 : int) <= n - i /\
                     n - (i + (1 : int)) < n - i) \/
                    (n - i = n - (i + (1 : int)) /\
                     (0 : int) <= j /\
                     j < j)) /\
                   ((((0 : int) <= j /\ j <= m) /\
                     j <= i + (1 : int) /\
                     i + (1 : int) <= n) /\
                    kmp_search_matches
                      a (i + (1 : int) - j)
                      p (0 : int) j /\
                    (!k : int.
                       (0 : int) <= k /\
                       k < i + (1 : int) - j ==>
                       ~kmp_search_matches
                         a k p (0 : int) m))
                 else
                   ((0 : int) <= j /\
                    j < &(LENGTH next)) /\
                   (((0 : int) <= n - i /\
                     n - i < n - i) \/
                    ((0 : int) <= j /\
                     kmp_search_get_int next j < j)) /\
                   ((((0 : int) <=
                       kmp_search_get_int next j /\
                      kmp_search_get_int next j <= m) /\
                     kmp_search_get_int next j <= i /\
                     i <= n) /\
                    kmp_search_matches
                      a (i - kmp_search_get_int next j)
                      p (0 : int)
                      (kmp_search_get_int next j) /\
                    (!k : int.
                       (0 : int) <= k /\
                       k < i - kmp_search_get_int next j ==>
                       ~kmp_search_matches
                         a k p (0 : int) m))
               else
                 !result : int.
                   (if j = m then
                      result = i - m
                    else
                      result = i)
                   ==>
                   kmp_search_first_occur p a result)``;
