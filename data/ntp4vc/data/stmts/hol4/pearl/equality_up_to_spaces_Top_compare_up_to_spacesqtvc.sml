(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/equality_up_to_spaces_Top_compare_up_to_spacesqtvc: a verification
  condition for comparing two character lists after removing spaces, including
  loop invariants, branch conditions, and decreasing measures. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val equality_spaces_to_nat_def = Define `
  equality_spaces_to_nat (z : int) =
    if z < 0 then 0 else Num z`;

val equality_up_to_spaces_Top_compare_up_to_spaces_vc =
  ``!(space : 'a)
      (eqc : 'a -> 'a -> bool)
      (remove_spaces : 'a list -> 'a list)
      (x : 'a list)
      (y : 'a list).
      (!a b : 'a. ((eqc a b = T) <=> (a = b))) /\
      (!s : 'a list.
         if &(LENGTH s) = (0 : int) then
           remove_spaces s = s
         else if eqc (EL 0 s) space = T then
           remove_spaces s = remove_spaces (DROP 1 s)
         else
           remove_spaces s =
             EL 0 s :: remove_spaces (DROP 1 s)) ==>
      let n = &(LENGTH x) in
      let m = &(LENGTH y) in
        (((0 : int) <= (0 : int) /\ (0 : int) <= n) /\
         ((0 : int) <= (0 : int) /\ (0 : int) <= m) /\
         ((remove_spaces x = remove_spaces y) <=>
          (remove_spaces (DROP 0 x) =
           remove_spaces (DROP 0 y)))) /\
        !j i : int.
          (((0 : int) <= i /\ i <= n) /\
           ((0 : int) <= j /\ j <= m) /\
           ((remove_spaces x = remove_spaces y) <=>
            (remove_spaces (DROP (equality_spaces_to_nat i) x) =
             remove_spaces (DROP (equality_spaces_to_nat j) y)))) ==>
          !o1 : bool.
            (if i < n then
               o1 = T
             else
               o1 = (if j < m then T else F)) ==>
            (if o1 = T then
               !o2 : bool.
                 (if i < n then
                    let o3 = space in
                    let o4 = EL (equality_spaces_to_nat i) x in
                      o2 = eqc o4 o3 /\
                      ((o2 = T) <=> (o4 = o3))
                  else
                    o2 = F) ==>
                 (if o2 = T then
                    (((0 : int) <= n - i + m - j /\
                      n - (i + (1 : int)) + m - j <
                        n - i + m - j) /\
                     ((0 : int) <= i + (1 : int) /\
                      i + (1 : int) <= n) /\
                     ((0 : int) <= j /\ j <= m) /\
                     ((remove_spaces x = remove_spaces y) <=>
                      (remove_spaces
                         (DROP
                            (equality_spaces_to_nat (i + (1 : int)))
                            x) =
                       remove_spaces
                         (DROP (equality_spaces_to_nat j) y))))
                  else
                    !o3 : bool.
                      (if j < m then
                         let o4 = space in
                         let o5 = EL (equality_spaces_to_nat j) y in
                           o3 = eqc o5 o4 /\
                           ((o3 = T) <=> (o5 = o4))
                       else
                         o3 = F) ==>
                      (if o3 = T then
                         (((0 : int) <= n - i + m - j /\
                           n - i + m - (j + (1 : int)) <
                             n - i + m - j) /\
                          ((0 : int) <= i /\ i <= n) /\
                          ((0 : int) <= j + (1 : int) /\
                           j + (1 : int) <= m) /\
                          ((remove_spaces x = remove_spaces y) <=>
                           (remove_spaces
                              (DROP (equality_spaces_to_nat i) x) =
                            remove_spaces
                              (DROP
                                 (equality_spaces_to_nat
                                    (j + (1 : int)))
                                 y))))
                       else
                         !o4 : bool.
                           (if i = n then
                              o4 = T
                            else
                              o4 = (if j = m then T else F)) ==>
                           (if o4 = T then
                              ~(remove_spaces x = remove_spaces y)
                            else
                              let o5 =
                                EL (equality_spaces_to_nat j) y
                              in
                              let o6 =
                                EL (equality_spaces_to_nat i) x
                              in
                              let o7 = eqc o6 o5 in
                                ((o7 = T) <=> (o6 = o5)) ==>
                                (if ~(o7 = T) then
                                   ~(remove_spaces x = remove_spaces y)
                                 else
                                   (((0 : int) <= n - i + m - j /\
                                     n - (i + (1 : int)) +
                                         m - (j + (1 : int)) <
                                       n - i + m - j) /\
                                    ((0 : int) <= i + (1 : int) /\
                                     i + (1 : int) <= n) /\
                                    ((0 : int) <= j + (1 : int) /\
                                     j + (1 : int) <= m) /\
                                    ((remove_spaces x =
                                      remove_spaces y) <=>
                                     (remove_spaces
                                        (DROP
                                           (equality_spaces_to_nat
                                              (i + (1 : int)))
                                           x) =
                                      remove_spaces
                                        (DROP
                                           (equality_spaces_to_nat
                                              (j + (1 : int)))
                                           y))))))))
             else
               remove_spaces x = remove_spaces y)``;
