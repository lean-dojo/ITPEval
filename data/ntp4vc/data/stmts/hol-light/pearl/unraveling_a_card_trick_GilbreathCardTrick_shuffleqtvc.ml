(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/unraveling_a_card_trick_GilbreathCardTrick_shuffleqtvc:
  the loop verification condition for constructing a riffle shuffle from two
  stacks while preserving its invariants and decreasing variant. This file
  contains no proof.
*)

let ntp4vc_gilbreath_shuffle_RULES,
    ntp4vc_gilbreath_shuffle_INDUCT,
    ntp4vc_gilbreath_shuffle_CASES =
  new_inductive_definition
   `(!l:int list.
       ntp4vc_gilbreath_shuffle l [] l) /\
    (!l:int list.
       ntp4vc_gilbreath_shuffle [] l l) /\
    (!a b c:int list.
     !x:int.
       ntp4vc_gilbreath_shuffle a b c
       ==>
       ntp4vc_gilbreath_shuffle
         (CONS x a) b (CONS x c)) /\
    (!a b c:int list.
     !x:int.
       ntp4vc_gilbreath_shuffle a b c
       ==>
       ntp4vc_gilbreath_shuffle
         a (CONS x b) (CONS x c))`;;

let statement =
 `!elts:A->int list.
  !c a' b' a b:A.
    let stack_length =
      \(s:A). (&(LENGTH (elts s)):int) in
    elts c = []
    ==>
    elts a' = []
    ==>
    elts b' = []
    ==>
    REVERSE (elts a) = APPEND (REVERSE (elts a)) (elts a') /\
    REVERSE (elts b) = APPEND (REVERSE (elts b)) (elts b') /\
    ntp4vc_gilbreath_shuffle (elts a') (elts b') (elts c) /\
    (!b'1 a'1 c1 b1 a1:A.
       REVERSE (elts a) = APPEND (REVERSE (elts a1)) (elts a'1) /\
       REVERSE (elts b) = APPEND (REVERSE (elts b1)) (elts b'1) /\
       ntp4vc_gilbreath_shuffle (elts a'1) (elts b'1) (elts c1)
       ==>
       !o1:bool.
         (if elts a1 = [] then
            o1 = (if elts b1 = [] then T else F)
          else
            o1 = F)
         ==>
         if ~(o1 = T) then
           !o2:bool.
             (if ~(elts a1 = []) then
                (elts b1 = [] ==> o2 = T)
              else
                o2 = F)
             ==>
             if o2 = T then
               ~(elts a1 = []) /\
               (!o3:int.
                  (if elts a1 = [] then F
                   else o3 = HD (elts a1))
                  ==>
                  !a'2:A.
                    elts a'2 = CONS o3 (elts a'1)
                    ==>
                    ~(elts a1 = []) /\
                    (!a2:A.
                     !o4:int.
                       (if elts a1 = [] then F
                        else
                          o4 = HD (elts a1) /\
                          elts a2 = TL (elts a1))
                       ==>
                       !c2:A.
                         elts c2 = CONS o4 (elts c1)
                         ==>
                         ((&0:int) <=
                            stack_length a1 + stack_length b1 /\
                          stack_length a2 + stack_length b1 <
                            stack_length a1 + stack_length b1) /\
                         REVERSE (elts a) =
                           APPEND (REVERSE (elts a2)) (elts a'2) /\
                         REVERSE (elts b) =
                           APPEND (REVERSE (elts b1)) (elts b'1) /\
                         ntp4vc_gilbreath_shuffle
                           (elts a'2) (elts b'1) (elts c2)))
             else
               ~(elts b1 = []) /\
               (!o3:int.
                  (if elts b1 = [] then F
                   else o3 = HD (elts b1))
                  ==>
                  !b'2:A.
                    elts b'2 = CONS o3 (elts b'1)
                    ==>
                    ~(elts b1 = []) /\
                    (!b2:A.
                     !o4:int.
                       (if elts b1 = [] then F
                        else
                          o4 = HD (elts b1) /\
                          elts b2 = TL (elts b1))
                       ==>
                       !c2:A.
                         elts c2 = CONS o4 (elts c1)
                         ==>
                         ((&0:int) <=
                            stack_length a1 + stack_length b1 /\
                          stack_length a1 + stack_length b2 <
                            stack_length a1 + stack_length b1) /\
                         REVERSE (elts a) =
                           APPEND (REVERSE (elts a1)) (elts a'1) /\
                         REVERSE (elts b) =
                           APPEND (REVERSE (elts b2)) (elts b'2) /\
                         ntp4vc_gilbreath_shuffle
                           (elts a'1) (elts b'2) (elts c2)))
         else
           elts a1 = [] /\
           elts b1 = [] /\
           ntp4vc_gilbreath_shuffle
             (REVERSE (elts a)) (REVERSE (elts b)) (elts c1))`;;
