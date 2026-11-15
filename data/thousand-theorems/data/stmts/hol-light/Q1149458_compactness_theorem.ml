(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1149458,
  "Compactness theorem": an arbitrary first-order theory is satisfiable if and
  only if each of its finite subtheories is satisfiable. This file contains no
  proof.
*)

let q1149458_term_INDUCT,q1149458_term_RECURSION = define_type
  "q1149458_term =
       Q1149458_Var num
     | Q1149458_Fun F (q1149458_term list)";;

let q1149458_form_INDUCT,q1149458_form_RECURSION = define_type
  "q1149458_form =
       Q1149458_Equal (F q1149458_term) (F q1149458_term)
     | Q1149458_Rel R ((F q1149458_term) list)
     | Q1149458_Not q1149458_form
     | Q1149458_And q1149458_form q1149458_form
     | Q1149458_Exists num q1149458_form";;

let q1149458_term_wellformed = new_recursive_definition
  q1149458_term_RECURSION
  `(q1149458_term_wellformed function_symbols function_arity
       (Q1149458_Var x) <=> T) /\
   (q1149458_term_wellformed function_symbols function_arity
       (Q1149458_Fun f arguments) <=>
      f IN function_symbols /\
      LENGTH arguments = function_arity f /\
      q1149458_term_list_wellformed
        function_symbols function_arity arguments) /\
   (q1149458_term_list_wellformed
       function_symbols function_arity [] <=> T) /\
   (q1149458_term_list_wellformed
       function_symbols function_arity (CONS term rest) <=>
      q1149458_term_wellformed function_symbols function_arity term /\
      q1149458_term_list_wellformed
        function_symbols function_arity rest)`;;

let q1149458_form_wellformed = new_recursive_definition
  q1149458_form_RECURSION
  `(q1149458_form_wellformed
       function_symbols relation_symbols function_arity relation_arity
       (Q1149458_Equal left right) <=>
      q1149458_term_wellformed function_symbols function_arity left /\
      q1149458_term_wellformed function_symbols function_arity right) /\
   (q1149458_form_wellformed
       function_symbols relation_symbols function_arity relation_arity
       (Q1149458_Rel relation arguments) <=>
      relation IN relation_symbols /\
      LENGTH arguments = relation_arity relation /\
      q1149458_term_list_wellformed
        function_symbols function_arity arguments) /\
   (q1149458_form_wellformed
       function_symbols relation_symbols function_arity relation_arity
       (Q1149458_Not p) <=>
      q1149458_form_wellformed
        function_symbols relation_symbols function_arity relation_arity p) /\
   (q1149458_form_wellformed
       function_symbols relation_symbols function_arity relation_arity
       (Q1149458_And p q) <=>
      q1149458_form_wellformed
        function_symbols relation_symbols function_arity relation_arity p /\
      q1149458_form_wellformed
        function_symbols relation_symbols function_arity relation_arity q) /\
   (q1149458_form_wellformed
       function_symbols relation_symbols function_arity relation_arity
       (Q1149458_Exists x p) <=>
      q1149458_form_wellformed
        function_symbols relation_symbols function_arity relation_arity p)`;;

let q1149458_term_has_variable = new_recursive_definition
  q1149458_term_RECURSION
  `(q1149458_term_has_variable x (Q1149458_Var y) <=> x = y) /\
   (q1149458_term_has_variable x (Q1149458_Fun f arguments) <=>
      q1149458_term_list_has_variable x arguments) /\
   (q1149458_term_list_has_variable x [] <=> F) /\
   (q1149458_term_list_has_variable x (CONS term rest) <=>
      q1149458_term_has_variable x term \/
      q1149458_term_list_has_variable x rest)`;;

let q1149458_form_has_free_variable = new_recursive_definition
  q1149458_form_RECURSION
  `(q1149458_form_has_free_variable x (Q1149458_Equal left right) <=>
      q1149458_term_has_variable x left \/
      q1149458_term_has_variable x right) /\
   (q1149458_form_has_free_variable x (Q1149458_Rel relation arguments) <=>
      q1149458_term_list_has_variable x arguments) /\
   (q1149458_form_has_free_variable x (Q1149458_Not p) <=>
      q1149458_form_has_free_variable x p) /\
   (q1149458_form_has_free_variable x (Q1149458_And p q) <=>
      q1149458_form_has_free_variable x p \/
      q1149458_form_has_free_variable x q) /\
   (q1149458_form_has_free_variable x (Q1149458_Exists y p) <=>
      ~(x = y) /\ q1149458_form_has_free_variable x p)`;;

let q1149458_is_sentence = new_definition
  `q1149458_is_sentence p <=>
     !x. ~(q1149458_form_has_free_variable x p)`;;

let q1149458_update = new_definition
  `q1149458_update x a (valuation:num->A) =
     \y. if y = x then a else valuation y`;;

let q1149458_term_value = new_recursive_definition
  q1149458_term_RECURSION
  `(q1149458_term_value function_interpretation valuation
       (Q1149458_Var x) =
      valuation x) /\
   (q1149458_term_value function_interpretation valuation
       (Q1149458_Fun f arguments) =
      function_interpretation f
        (q1149458_term_list_value
           function_interpretation valuation arguments)) /\
   (q1149458_term_list_value function_interpretation valuation [] = []) /\
   (q1149458_term_list_value function_interpretation valuation
       (CONS term rest) =
      CONS (q1149458_term_value function_interpretation valuation term)
           (q1149458_term_list_value
              function_interpretation valuation rest))`;;

let q1149458_holds = new_recursive_definition
  q1149458_form_RECURSION
  `(q1149458_holds domain function_interpretation relation_interpretation
       valuation (Q1149458_Equal left right) <=>
      q1149458_term_value function_interpretation valuation left =
      q1149458_term_value function_interpretation valuation right) /\
   (q1149458_holds domain function_interpretation relation_interpretation
       valuation (Q1149458_Rel relation arguments) <=>
      relation_interpretation relation
        (q1149458_term_list_value
           function_interpretation valuation arguments)) /\
   (q1149458_holds domain function_interpretation relation_interpretation
       valuation (Q1149458_Not p) <=>
      ~(q1149458_holds domain function_interpretation relation_interpretation
          valuation p)) /\
   (q1149458_holds domain function_interpretation relation_interpretation
       valuation (Q1149458_And p q) <=>
      q1149458_holds domain function_interpretation relation_interpretation
        valuation p /\
      q1149458_holds domain function_interpretation relation_interpretation
        valuation q) /\
   (q1149458_holds domain function_interpretation relation_interpretation
       valuation (Q1149458_Exists x p) <=>
      ?a. a IN domain /\
          q1149458_holds domain
            function_interpretation relation_interpretation
            (q1149458_update x a valuation) p)`;;

let Q1149458_COMPACTNESS_THEOREM =
 `let is_satisfiable =
    \(function_symbols:F->bool) (relation_symbols:R->bool)
     (function_arity:F->num) (theory:(F,R)q1149458_form->bool).
       ?domain:(num#F#R)->bool.
       ?function_interpretation:F->((num#F#R)list)->(num#F#R).
       ?relation_interpretation:R->((num#F#R)list)->bool.
         (?a:num#F#R. a IN domain) /\
         (!f:F. !arguments:(num#F#R)list.
            f IN function_symbols /\
            LENGTH arguments = function_arity f /\
            ALL (\a:num#F#R. a IN domain) arguments
            ==> function_interpretation f arguments IN domain) /\
         (!p:(F,R)q1149458_form.
            p IN theory
            ==> !valuation:num->(num#F#R).
                  (!x:num. valuation x IN domain)
                  ==> q1149458_holds
                        domain function_interpretation
                        relation_interpretation valuation p) in
  !function_symbols:F->bool.
  !relation_symbols:R->bool.
  !function_arity:F->num.
  !relation_arity:R->num.
  !theory:(F,R)q1149458_form->bool.
    (!p:(F,R)q1149458_form.
       p IN theory
       ==> q1149458_form_wellformed
             function_symbols relation_symbols
             function_arity relation_arity p /\
           q1149458_is_sentence p)
    ==> (is_satisfiable
           function_symbols relation_symbols function_arity theory <=>
         !finite_theory:(F,R)q1149458_form->bool.
           FINITE finite_theory /\ finite_theory SUBSET theory
           ==> is_satisfiable
                 function_symbols relation_symbols
                 function_arity finite_theory)`;;
