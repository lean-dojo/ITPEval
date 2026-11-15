(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/unraveling_a_card_trick_GilbreathCardTrick_shuffleqtvc: the loop
  verification condition for constructing a riffle shuffle from two integer
  stacks while preserving its invariants and decreasing variant. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val (ntp4vc_gilbreath_shuffle_rules,
     ntp4vc_gilbreath_shuffle_ind,
     ntp4vc_gilbreath_shuffle_cases) =
  Hol_reln `
    (!l : 'a list.
       ntp4vc_gilbreath_shuffle l [] l) /\
    (!l : 'a list.
       ntp4vc_gilbreath_shuffle [] l l) /\
    (!x : 'a.
     !a b c : 'a list.
       ntp4vc_gilbreath_shuffle a b c ==>
       ntp4vc_gilbreath_shuffle (x::a) b (x::c)) /\
    (!x : 'a.
     !a b c : 'a list.
       ntp4vc_gilbreath_shuffle a b c ==>
       ntp4vc_gilbreath_shuffle a (x::b) (x::c))
  `;

val unraveling_a_card_trick_GilbreathCardTrick_shuffleqtvc_statement =
  ``!(elts : 'stack -> int list)
      (c a_prime b_prime a b : 'stack).
      let stack_length =
        \s : 'stack. &(LENGTH (elts s))
      in
        elts c = ([] : int list) ==>
        elts a_prime = ([] : int list) ==>
        elts b_prime = ([] : int list) ==>
        REVERSE (elts a) =
          REVERSE (elts a) ++ elts a_prime /\
        REVERSE (elts b) =
          REVERSE (elts b) ++ elts b_prime /\
        ntp4vc_gilbreath_shuffle
          (elts a_prime) (elts b_prime) (elts c) /\
        (!b_prime1 a_prime1 c1 b1 a1 : 'stack.
           REVERSE (elts a) =
             REVERSE (elts a1) ++ elts a_prime1 /\
           REVERSE (elts b) =
             REVERSE (elts b1) ++ elts b_prime1 /\
           ntp4vc_gilbreath_shuffle
             (elts a_prime1) (elts b_prime1) (elts c1)
           ==>
           !o1 : bool.
             (if elts a1 = ([] : int list) then
                o1 =
                  (if elts b1 = ([] : int list) then T else F)
              else
                o1 = F)
             ==>
             if ~(o1 = T) then
               !o2 : bool.
                 (if ~(elts a1 = ([] : int list)) then
                    elts b1 = ([] : int list) ==> o2 = T
                  else
                    o2 = F)
                 ==>
                 if o2 = T then
                   ~(elts a1 = ([] : int list)) /\
                   (!o3 : int.
                      (case elts a1 of
                         [] => F
                       | x::t => o3 = x)
                      ==>
                      !a_prime2 : 'stack.
                        elts a_prime2 = o3::elts a_prime1
                        ==>
                        ~(elts a1 = ([] : int list)) /\
                        (!a2 : 'stack.
                         !o4 : int.
                           (case elts a1 of
                              [] => F
                            | x::t =>
                                o4 = x /\ elts a2 = t)
                           ==>
                           !c2 : 'stack.
                             elts c2 = o4::elts c1
                             ==>
                             (((0 : int) <=
                                 stack_length a1 +
                                 stack_length b1 /\
                               stack_length a2 +
                                 stack_length b1 <
                               stack_length a1 +
                                 stack_length b1) /\
                              REVERSE (elts a) =
                                REVERSE (elts a2) ++
                                elts a_prime2 /\
                              REVERSE (elts b) =
                                REVERSE (elts b1) ++
                                elts b_prime1 /\
                              ntp4vc_gilbreath_shuffle
                                (elts a_prime2)
                                (elts b_prime1)
                                (elts c2))))
                 else
                   ~(elts b1 = ([] : int list)) /\
                   (!o3 : int.
                      (case elts b1 of
                         [] => F
                       | x::t => o3 = x)
                      ==>
                      !b_prime2 : 'stack.
                        elts b_prime2 = o3::elts b_prime1
                        ==>
                        ~(elts b1 = ([] : int list)) /\
                        (!b2 : 'stack.
                         !o4 : int.
                           (case elts b1 of
                              [] => F
                            | x::t =>
                                o4 = x /\ elts b2 = t)
                           ==>
                           !c2 : 'stack.
                             elts c2 = o4::elts c1
                             ==>
                             (((0 : int) <=
                                 stack_length a1 +
                                 stack_length b1 /\
                               stack_length a1 +
                                 stack_length b2 <
                               stack_length a1 +
                                 stack_length b1) /\
                              REVERSE (elts a) =
                                REVERSE (elts a1) ++
                                elts a_prime1 /\
                              REVERSE (elts b) =
                                REVERSE (elts b2) ++
                                elts b_prime2 /\
                              ntp4vc_gilbreath_shuffle
                                (elts a_prime1)
                                (elts b_prime2)
                                (elts c2))))
             else
               elts a1 = ([] : int list) /\
               elts b1 = ([] : int list) /\
               ntp4vc_gilbreath_shuffle
                 (REVERSE (elts a))
                 (REVERSE (elts b))
                 (elts c1))``;
