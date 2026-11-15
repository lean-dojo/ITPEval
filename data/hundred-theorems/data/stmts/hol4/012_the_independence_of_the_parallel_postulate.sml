(*
  Statement-only formalization of "The Independence of the Parallel Postulate" from Hundred
  Theorems item 012. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory;

val independence_of_parallel_postulate =
  ``?betw : real # real -> real # real -> real # real -> bool.
    ?cong :
      real # real -> real # real -> real # real -> real # real -> bool.
      (!a b. cong a b b a) /\
      (!a b p q r s.
         cong a b p q /\ cong a b r s ==> cong p q r s) /\
      (!a b c. cong a b c c ==> a = b) /\
      (!q a b c. ?x. betw q a x /\ cong a x b c) /\
      (!a b c d a' b' c' d'.
         ~(a = b) /\
         betw a b c /\ betw a' b' c' /\
         cong a b a' b' /\ cong b c b' c' /\
         cong a d a' d' /\ cong b d b' d'
         ==> cong c d c' d') /\
      (!a b. betw a b a ==> a = b) /\
      (!a b c p q.
         betw a p c /\ betw b q c
         ==> ?x. betw p x b /\ betw q x a) /\
      (?a b c. ~betw a b c /\ ~betw b c a /\ ~betw c a b) /\
      (!p q a b c.
         ~(p = q) /\
         cong a p a q /\ cong b p b q /\ cong c p c q
         ==> betw a b c \/ betw b c a \/ betw c a b) /\
      ~(!a b c d t.
          betw a d t /\ betw b d c /\ ~(a = d)
          ==> ?x y. betw a b x /\ betw a c y /\ betw x t y) /\
      (!X Y : real # real -> bool.
         (?a. !x y. X x /\ Y y ==> betw a x y)
         ==> ?b. !x y. X x /\ Y y ==> betw x b y)``;
