(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.let_clause_10471, catalog title "bigops.let_clause_10471": a nested
  proposition about Boolean-selected natural-number products and mutually
  inverse selected-index maps, concluding the natural-number
  quotient-remainder identity. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_bigops_source_div_def = Define `
  logipedia_bigops_source_div n m =
    if m = 0 then SUC n else n DIV m
`;

val logipedia_bigops_source_mod_def = Define `
  logipedia_bigops_source_mod n m =
    if m = 0 then n else n MOD m
`;

val logipedia_bigops_nat_bigop_def = Define `
  (logipedia_bigops_nat_bigop 0 (p : num -> bool) (f : num -> num) = 1) /\
  (logipedia_bigops_nat_bigop (SUC n) p f =
    if p n then
      f n * logipedia_bigops_nat_bigop n p f
    else
      logipedia_bigops_nat_bigop n p f)
`;

val logipedia_bigops_sub_hk_def = Define `
  logipedia_bigops_sub_hk
    (h : num -> num)
    (k : num -> num)
    (n1 : num)
    (n2 : num)
    (p1 : num -> bool)
    (p2 : num -> bool)
    (f1 : num -> num)
    (f2 : num -> num) <=>
  !i : num.
    i < n1
    ==>
    p1 i = T
    ==>
    (h i < n2 /\ p2 (h i) = T) /\ k (h i) = i
`;

val logipedia_bigops_iso_def = Define `
  logipedia_bigops_iso
    (n1 : num)
    (n2 : num)
    (p1 : num -> bool)
    (p2 : num -> bool)
    (f1 : num -> num)
    (f2 : num -> num) <=>
  ?h k : num -> num.
    ((!i : num.
        i < n1
        ==>
        p1 i = T
        ==>
        f1 i = f2 (h i)) /\
      logipedia_bigops_sub_hk h k n1 n2 p1 p2 f1 f2) /\
    logipedia_bigops_sub_hk k h n2 n1 p2 p1 f2 f1
`;

val bigops_let_clause_10471 =
  ``!n1 n2 : num.
      !(p1 : num -> bool) (p2 : num -> bool).
      !(f1 : num -> num) (f2 : num -> num).
        logipedia_bigops_iso n1 n2 p1 p2 f1 f2
        ==>
        !h : num -> num.
          (?k : num -> num.
             (((!j : num.
                  j < n1
                  ==>
                  p1 j = T
                  ==>
                  f1 j = f2 (h j)) /\
                logipedia_bigops_sub_hk
                  h k n1 n2 p1 p2 f1 f2) /\
              logipedia_bigops_sub_hk
                k h n2 n1 p2 p1 f2 f1))
          ==>
          !k : num -> num.
            (((!j : num.
                 j < n1
                 ==>
                 p1 j = T
                 ==>
                 f1 j = f2 (h j)) /\
               logipedia_bigops_sub_hk
                 h k n1 n2 p1 p2 f1 f2) /\
             logipedia_bigops_sub_hk
               k h n2 n1 p2 p1 f2 f1)
            ==>
            ((!j : num.
                j < n1
                ==>
                p1 j = T
                ==>
                f1 j = f2 (h j)) /\
              logipedia_bigops_sub_hk
                h k n1 n2 p1 p2 f1 f2)
            ==>
            (!j : num.
               j < n1
               ==>
               p1 j = T
               ==>
               f1 j = f2 (h j))
            ==>
            !i : num.
              !m : num.
                (!f : num -> bool.
                   0 <= n1
                   ==>
                   logipedia_bigops_sub_hk
                     h k 0 m p1 f f1 f2
                   ==>
                   logipedia_bigops_sub_hk
                     k h m 0 f p1 f2 f1
                   ==>
                   logipedia_bigops_nat_bigop 0 p1 f1 =
                   logipedia_bigops_nat_bigop m f f2)
                ==>
                !p20 : num -> bool.
                  0 <= n1
                  ==>
                  logipedia_bigops_sub_hk
                    h k 0 (SUC m) p1 p20 f1 f2
                  ==>
                  logipedia_bigops_sub_hk
                    k h (SUC m) 0 p20 p1 f2 f1
                  ==>
                  !x2571 x2572 : num.
                    x2571 =
                    x2572 *
                      logipedia_bigops_source_div x2571 x2572 +
                    logipedia_bigops_source_mod x2571 x2572``;
