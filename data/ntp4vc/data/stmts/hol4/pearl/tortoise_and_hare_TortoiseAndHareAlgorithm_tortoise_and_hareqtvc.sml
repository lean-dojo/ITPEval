(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/tortoise_and_hare_TortoiseAndHareAlgorithm_tortoise_and_hareqtvc:
  the verification condition for Floyd's tortoise-and-hare cycle-detection
  loops, preserving the sequence invariants used to recover the cycle entry
  and period. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val tortoise_and_hare_TortoiseAndHareAlgorithm_tortoise_and_hare_vc =
  ``!(f : int -> int) (m x0 mu lambda : int).
      (0 : int) < m ==>
      (!z : int.
         (0 : int) <= z /\ z < m ==>
         (0 : int) <= f z /\ f z < m) ==>
      ((0 : int) <= x0 /\ x0 < m) ==>
      (0 : int) <= mu ==>
      mu < m ==>
      (1 : int) <= lambda ==>
      lambda <= m ==>
      mu + lambda <= m ==>
      let x = \i : int. FUNPOW f (Num i) x0
      in
        x (mu + lambda) = x mu ==>
        (!i j : int.
           (0 : int) <= i /\ i < j /\ j < mu + lambda ==>
           ~(x i = x j)) ==>
        (1 : int) <= (1 : int) /\
        (1 : int) <= mu + lambda /\
        f x0 = x (1 : int) /\
        f (f x0) = x ((2 : int) * (1 : int)) /\
        (!i : int.
           (1 : int) <= i /\ i < (1 : int) ==>
           ~(x i = x ((2 : int) * i))) /\
        (!n : int.
           (((1 : int) <= n /\ n <= mu + lambda) /\
            (!i : int.
               (1 : int) <= i /\ i < n ==>
               ~(x i = x ((2 : int) * i)))) ==>
           if ~(x n = x ((2 : int) * n)) then
             ~(mu + lambda < n + (1 : int)) /\
             (~(mu + lambda < n + (1 : int)) ==>
              (((0 : int) <= mu + lambda - n /\
                mu + lambda - (n + (1 : int)) <
                  mu + lambda - n) /\
               ((1 : int) <= n + (1 : int) /\
                n + (1 : int) <= mu + lambda) /\
               f (x n) = x (n + (1 : int)) /\
               f (f (x ((2 : int) * n))) =
                 x ((2 : int) * (n + (1 : int))) /\
               (!i : int.
                  (1 : int) <= i /\ i < n + (1 : int) ==>
                  ~(x i = x ((2 : int) * i)))))
           else
             ((((0 : int) <= (0 : int) /\ (0 : int) <= mu) /\
               (x0 = x (0 : int) /\ x n = x (n + (0 : int))) /\
               (!j : int.
                  (0 : int) <= j /\ j < (0 : int) ==>
                  ~(x j = x (n + j))) /\
               (!j : int.
                  (0 : int) < j /\ j < (0 : int) ==>
                  ~(x (n + j) = x n))) /\
              (!lam i : int.
                 (((0 : int) <= i /\ i <= mu) /\
                  (!j : int.
                     (0 : int) <= j /\ j < i ==>
                     ~(x j = x (n + j))) /\
                  (if lam = (0 : int) then
                     !j : int.
                       (0 : int) < j /\ j < i ==>
                       ~(x (n + j) = x n)
                   else
                     lam = lambda)) ==>
                 if ~(x i = x (n + i)) then
                   !o1 : bool.
                     (if lam = (0 : int) then
                        o1 =
                          (if (0 : int) < i then
                             if x (n + i) = x n then T else F
                           else
                             F)
                      else
                        o1 = F) ==>
                     if o1 = T then
                       (((0 : int) <= mu - i /\
                         mu - (i + (1 : int)) < mu - i) /\
                        ((0 : int) <= i + (1 : int) /\
                         i + (1 : int) <= mu) /\
                        (f (x i) = x (i + (1 : int)) /\
                         f (x (n + i)) =
                           x (n + (i + (1 : int)))) /\
                        (!j : int.
                           (0 : int) <= j /\ j < i + (1 : int) ==>
                           ~(x j = x (n + j))) /\
                        (if i = (0 : int) then
                           !j : int.
                             (0 : int) < j /\ j < i + (1 : int) ==>
                             ~(x (n + j) = x n)
                         else
                           i = lambda))
                     else
                       (((0 : int) <= mu - i /\
                         mu - (i + (1 : int)) < mu - i) /\
                        ((0 : int) <= i + (1 : int) /\
                         i + (1 : int) <= mu) /\
                        (f (x i) = x (i + (1 : int)) /\
                         f (x (n + i)) =
                           x (n + (i + (1 : int)))) /\
                        (!j : int.
                           (0 : int) <= j /\ j < i + (1 : int) ==>
                           ~(x j = x (n + j))) /\
                        (if lam = (0 : int) then
                           !j : int.
                             (0 : int) < j /\ j < i + (1 : int) ==>
                             ~(x (n + j) = x n)
                         else
                           lam = lambda))
                 else
                   !l : int.
                     (if lam = (0 : int) then l = n else l = lam) ==>
                     ((((0 : int) <= i /\ i < m) /\
                       ((1 : int) <= l /\ l <= m) /\
                       i + l <= m /\
                       x (i + l) = x i) /\
                      (!i1 j : int.
                         (0 : int) <= i1 /\ i1 < j /\ j < i + l ==>
                         ~(x i1 = x j))))))``;
