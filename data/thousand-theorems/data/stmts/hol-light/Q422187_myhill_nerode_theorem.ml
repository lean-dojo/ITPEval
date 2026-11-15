(*
  Statement-only formalization of Thousand Theorems corpus artifact Q422187,
  "Myhill–Nerode theorem": a language over an arbitrary, possibly empty,
  alphabet is regular if and only if its set of left quotients by words is
  finite. This file contains no proof.
*)

let q422187_run = new_recursive_definition list_RECURSION
  `(q422187_run transition state [] = state) /\
   (q422187_run transition state (CONS symbol rest) =
      q422187_run transition (transition state symbol) rest)`;;

let q422187_left_quotient = new_definition
  `q422187_left_quotient alphabet language prefix =
     \suffix.
       ALL alphabet suffix /\
       language (APPEND prefix suffix)`;;

let q422187_is_regular = new_definition
  `q422187_is_regular (alphabet:A->bool) (language:A list->bool) <=>
     ?state_count start:num.
     ?transition:num->A->num.
     ?accepting:num->bool.
       start < state_count /\
       (!state symbol.
          state < state_count /\ alphabet symbol
          ==> transition state symbol < state_count) /\
       (!word:A list.
          ALL alphabet word
          ==> (language word <=>
               accepting (q422187_run transition start word)))`;;

let Q422187_MYHILL_NERODE_THEOREM =
  `!alphabet:A->bool. !language:A list->bool.
     q422187_is_regular alphabet language <=>
     FINITE
       (IMAGE (q422187_left_quotient alphabet language)
              {prefix:A list | ALL alphabet prefix})`;;
