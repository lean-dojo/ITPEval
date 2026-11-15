(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/unraveling_a_card_trick_GilbreathCardTrick_card_trickqtvc:
  the card-trick verification condition for cutting an ordered deck into
  stacks and riffle-shuffling the reversed parts. This file contains no proof.
*)

let ntp4vc_gilbreath_nth = new_definition
 `ntp4vc_gilbreath_nth (xs:int list) (i:int) =
    if num_of_int i < LENGTH xs
    then SOME (EL (num_of_int i) xs)
    else NONE`;;

let ntp4vc_gilbreath_suit_ordered = new_definition
 `ntp4vc_gilbreath_suit_ordered
    (m:int) (n:int) (xs:int list) <=>
    !i j:int.
      (&0:int) <= i /\ i < n
      ==>
      (&0:int) <= j /\ j < m
      ==>
      ntp4vc_gilbreath_nth xs (i * m + j) = SOME j`;;

let ntp4vc_gilbreath_suit_sorted = new_definition
 `ntp4vc_gilbreath_suit_sorted
    (m:int) (n:int) (xs:int list) <=>
    (!i v:int.
       ntp4vc_gilbreath_nth xs i = SOME v
       ==>
       (&0:int) <= v /\ v < m) /\
    (!i j1 j2:int.
       (&0:int) <= i /\ i < n
       ==>
       (&0:int) <= j1 /\ j1 < m
       ==>
       (&0:int) <= j2 /\ j2 < m
       ==>
       ~(ntp4vc_gilbreath_nth xs (i * m + j1) =
         ntp4vc_gilbreath_nth xs (i * m + j2)))`;;

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
 `!m n:int.
  !elts:A->int list.
  !a d0:A.
    (&0:int) < m
    ==>
    (&0:int) <= n
    ==>
    (!ordered c d b:int list.
       (&(LENGTH ordered):int) = n * m
       ==>
       ntp4vc_gilbreath_suit_ordered m n ordered
       ==>
       ordered = APPEND c d
       ==>
       ntp4vc_gilbreath_shuffle c (REVERSE d) b
       ==>
       ntp4vc_gilbreath_suit_sorted m n b)
    ==>
    let stack_length =
      \(s:A). (&(LENGTH (elts s)):int) in
    stack_length a = n * m
    ==>
    ntp4vc_gilbreath_suit_ordered m n (elts a)
    ==>
    elts d0 = []
    ==>
    ((?result:int.
        (&0:int) <= result /\ result <= n * m) /\
     (!cut:int.
        (&0:int) <= cut /\ cut <= n * m
        ==>
        (((&1:int) <= cut + (&1:int)
          ==>
          (stack_length a = n * m - (&1:int) + (&1:int) /\
           stack_length d0 = (&1:int) - (&1:int) /\
           elts a = APPEND (REVERSE (elts d0)) (elts a)) /\
          (!d1 a1:A.
             ((!i:int.
                 (((&1:int) <= i /\ i <= cut) /\
                  stack_length a1 = n * m - i + (&1:int) /\
                  stack_length d1 = i - (&1:int) /\
                  elts a = APPEND (REVERSE (elts d1)) (elts a1))
                 ==>
                 ~(elts a1 = []) /\
                 (!a2:A.
                  !o1:int.
                    elts a1 = CONS o1 (elts a2)
                    ==>
                    !d2:A.
                      elts d2 = CONS o1 (elts d1)
                      ==>
                      stack_length a2 =
                        n * m - (i + (&1:int)) + (&1:int) /\
                      stack_length d2 =
                        i + (&1:int) - (&1:int) /\
                      elts a =
                        APPEND (REVERSE (elts d2)) (elts a2))) /\
              ((stack_length a1 =
                  n * m - (cut + (&1:int)) + (&1:int) /\
                stack_length d1 =
                  cut + (&1:int) - (&1:int) /\
                elts a =
                  APPEND (REVERSE (elts d1)) (elts a1))
               ==>
               (!d2 a2 result:A.
                  elts a2 = [] /\
                  elts d2 = [] /\
                  ntp4vc_gilbreath_shuffle
                    (REVERSE (elts a1))
                    (REVERSE (elts d1))
                    (elts result)
                  ==>
                  stack_length result = n * m /\
                  ntp4vc_gilbreath_suit_sorted
                    m n (elts result)))))) /\
         (cut + (&1:int) < (&1:int)
          ==>
          (!d1 a1 result:A.
             elts a1 = [] /\
             elts d1 = [] /\
             ntp4vc_gilbreath_shuffle
               (REVERSE (elts a))
               (REVERSE (elts d0))
               (elts result)
             ==>
             stack_length result = n * m /\
             ntp4vc_gilbreath_suit_sorted
               m n (elts result))))))`;;
