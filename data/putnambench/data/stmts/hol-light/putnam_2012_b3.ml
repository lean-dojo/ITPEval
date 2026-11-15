(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_b3:
  every round-robin tournament on 2n teams admits an injective choice of one
  winning team from each of its 2n-1 days. This file contains no proof.
*)

let statement =
  `!nmatchupsgames:
       num->(num->num->num)->bool.
   !nmatchupsall:
       num->(num->num->num)->bool.
   !nmatchupswins:
       num->(num->num->num)->(num->num->bool)->bool.
   !nmatchupswinschoices:
       num->(num->num->num)->(num->num->bool)->bool.
     (!n:num. !matchups:num->num->num.
        (nmatchupsgames n matchups <=>
         !d t:num.
           d < 2 * n - 1 /\ t < 2 * n
           ==>
           matchups d t < 2 * n /\
           ~(matchups d t = t) /\
           matchups d (matchups d t) = t)) /\
     (!n:num. !matchups:num->num->num.
        (nmatchupsall n matchups <=>
         !t1 t2:num.
           t1 < 2 * n /\ t2 < 2 * n /\ ~(t1 = t2)
           ==> ?d:num. d < 2 * n - 1 /\ matchups d t1 = t2)) /\
     (!n:num. !matchups:num->num->num. !wins:num->num->bool.
        (nmatchupswins n matchups wins <=>
         !d t:num.
           d < 2 * n - 1 /\ t < 2 * n
           ==> (wins d t <=> ~(wins d (matchups d t))))) /\
     (!n:num. !matchups:num->num->num. !wins:num->num->bool.
        (nmatchupswinschoices n matchups wins <=>
         ?choices:num->num.
           (!d:num.
              d < 2 * n - 1
              ==> choices d < 2 * n /\ wins d (choices d)) /\
           (!d1 d2:num.
              d1 < 2 * n - 1 /\ d2 < 2 * n - 1 /\
              choices d1 = choices d2
              ==> d1 = d2)))
     ==>
     (((!n:num.
          1 <= n
          ==>
          !matchups:num->num->num. !wins:num->num->bool.
            nmatchupsgames n matchups /\
            nmatchupsall n matchups /\
            nmatchupswins n matchups wins
            ==> nmatchupswinschoices n matchups wins)
       <=> T))`;;
