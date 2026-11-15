(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/unraveling_a_card_trick_GilbreathCardTrick_card_trickqtvc: the card
  trick verification condition for cutting an ordered deck into stacks,
  reversing the cut prefix, riffle-shuffling the two parts, and obtaining
  suit-sorted output. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory optionTheory;

val gct_nth_opt_def = Define `
  gct_nth_opt (xs : int list) (i : int) =
    if i < (0 : int) then
      (NONE : int option)
    else if Num i < LENGTH xs then
      SOME (EL (Num i) xs)
    else
      NONE`;

val gct_suit_ordered_def = Define `
  gct_suit_ordered (n : int) (m : int) (xs : int list) <=>
    !i j : int.
      (0 : int) <= i /\ i < n ==>
      (0 : int) <= j /\ j < m ==>
      gct_nth_opt xs (i * m + j) = SOME j`;

val gct_suit_sorted_def = Define `
  gct_suit_sorted (n : int) (m : int) (xs : int list) <=>
    (!i v : int.
       gct_nth_opt xs i = SOME v ==>
       (0 : int) <= v /\ v < m) /\
    (!i j1 j2 : int.
       (0 : int) <= i /\ i < n ==>
       (0 : int) <= j1 /\ j1 < m ==>
       (0 : int) <= j2 /\ j2 < m ==>
       ~(gct_nth_opt xs (i * m + j1) =
         gct_nth_opt xs (i * m + j2)))`;

val (gct_shuffle_rules,
     gct_shuffle_ind,
     gct_shuffle_cases) =
  Hol_reln `
    (!l : 'a list.
       gct_shuffle l [] l) /\
    (!l : 'a list.
       gct_shuffle [] l l) /\
    (!x : 'a.
     !a b c : 'a list.
       gct_shuffle a b c ==>
       gct_shuffle (x::a) b (x::c)) /\
    (!x : 'a.
     !a b c : 'a list.
       gct_shuffle a b c ==>
       gct_shuffle a (x::b) (x::c))
  `;

val unraveling_a_card_trick_GilbreathCardTrick_card_trick_vc =
  ``!(m : int) (n : int) (elts : 'stack -> int list).
      (0 : int) < m ==>
      (0 : int) <= n ==>
      (!ordered c d shuffled : int list.
         &(LENGTH ordered) = n * m ==>
         gct_suit_ordered n m ordered ==>
         ordered = c ++ d ==>
         gct_shuffle c (REVERSE d) shuffled ==>
         gct_suit_sorted n m shuffled) ==>
      !a d' : 'stack.
        &(LENGTH (elts a)) = n * m ==>
        gct_suit_ordered n m (elts a) ==>
        elts d' = ([] : int list) ==>
        (?result : int.
           (0 : int) <= result /\ result <= n * m) /\
        (!cut : int.
           (0 : int) <= cut /\ cut <= n * m ==>
           (((1 : int) <= cut + (1 : int) ==>
             (&(LENGTH (elts a)) =
                n * m - (1 : int) + (1 : int) /\
              &(LENGTH (elts d')) =
                (1 : int) - (1 : int) /\
              elts a = REVERSE (elts d') ++ elts a) /\
             (!d1 a1 : 'stack.
                (!i : int.
                   (((1 : int) <= i /\ i <= cut) /\
                    &(LENGTH (elts a1)) =
                      n * m - i + (1 : int) /\
                    &(LENGTH (elts d1)) =
                      i - (1 : int) /\
                    elts a =
                      REVERSE (elts d1) ++ elts a1)
                   ==>
                   ~(elts a1 = ([] : int list)) /\
                   (!a2 : 'stack.
                    !o1 : int.
                      (case elts a1 of
                         [] => F
                       | x::t => o1 = x /\ elts a2 = t)
                      ==>
                      !d2 : 'stack.
                        elts d2 = o1::elts d1 ==>
                        &(LENGTH (elts a2)) =
                          n * m - (i + (1 : int)) + (1 : int) /\
                        &(LENGTH (elts d2)) =
                          i + (1 : int) - (1 : int) /\
                        elts a =
                          REVERSE (elts d2) ++ elts a2)) /\
                ((&(LENGTH (elts a1)) =
                    n * m - (cut + (1 : int)) + (1 : int) /\
                  &(LENGTH (elts d1)) =
                    cut + (1 : int) - (1 : int) /\
                  elts a =
                    REVERSE (elts d1) ++ elts a1)
                 ==>
                 !d2 a2 result : 'stack.
                   elts a2 = ([] : int list) /\
                   elts d2 = ([] : int list) /\
                   gct_shuffle
                     (REVERSE (elts a1))
                     (REVERSE (elts d1))
                     (elts result)
                   ==>
                   &(LENGTH (elts result)) = n * m /\
                   gct_suit_sorted n m (elts result))))) /\
            (cut + (1 : int) < (1 : int) ==>
             !d1 a1 result : 'stack.
               elts a1 = ([] : int list) /\
               elts d1 = ([] : int list) /\
               gct_shuffle
                 (REVERSE (elts a))
                 (REVERSE (elts d'))
                 (elts result)
               ==>
               &(LENGTH (elts result)) = n * m /\
               gct_suit_sorted n m (elts result)))``;
