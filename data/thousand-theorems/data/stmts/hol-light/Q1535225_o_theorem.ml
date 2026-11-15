(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1535225
  (thousand-theorems__hol-light__Q1535225), "Łoś' theorem": a first-order
  sentence holds in an ultraproduct exactly when the set of component
  structures in which it holds belongs to the ultrafilter. This file contains
  no proof.
*)

let q1535225_term_INDUCT,q1535225_term_RECURSION = define_type
  "q1535225_term =
       Q1535225_Var num
     | Q1535225_Fun F (q1535225_term list)";;

let q1535225_form_INDUCT,q1535225_form_RECURSION = define_type
  "q1535225_form =
       Q1535225_Equal (F q1535225_term) (F q1535225_term)
     | Q1535225_Rel R ((F q1535225_term) list)
     | Q1535225_Not q1535225_form
     | Q1535225_And q1535225_form q1535225_form
     | Q1535225_Exists num q1535225_form";;

let q1535225_term_wellformed = new_recursive_definition
  q1535225_term_RECURSION
  `(q1535225_term_wellformed function_arity (Q1535225_Var x) <=> T) /\
   (q1535225_term_wellformed function_arity
       (Q1535225_Fun f arguments) <=>
      LENGTH arguments = function_arity f /\
      q1535225_term_list_wellformed function_arity arguments) /\
   (q1535225_term_list_wellformed function_arity [] <=> T) /\
   (q1535225_term_list_wellformed function_arity (CONS term rest) <=>
      q1535225_term_wellformed function_arity term /\
      q1535225_term_list_wellformed function_arity rest)`;;

let q1535225_form_wellformed = new_recursive_definition
  q1535225_form_RECURSION
  `(q1535225_form_wellformed function_arity relation_arity
       (Q1535225_Equal left right) <=>
      q1535225_term_wellformed function_arity left /\
      q1535225_term_wellformed function_arity right) /\
   (q1535225_form_wellformed function_arity relation_arity
       (Q1535225_Rel relation arguments) <=>
      LENGTH arguments = relation_arity relation /\
      q1535225_term_list_wellformed function_arity arguments) /\
   (q1535225_form_wellformed function_arity relation_arity
       (Q1535225_Not p) <=>
      q1535225_form_wellformed function_arity relation_arity p) /\
   (q1535225_form_wellformed function_arity relation_arity
       (Q1535225_And p q) <=>
      q1535225_form_wellformed function_arity relation_arity p /\
      q1535225_form_wellformed function_arity relation_arity q) /\
   (q1535225_form_wellformed function_arity relation_arity
       (Q1535225_Exists x p) <=>
      q1535225_form_wellformed function_arity relation_arity p)`;;

let q1535225_term_has_variable = new_recursive_definition
  q1535225_term_RECURSION
  `(q1535225_term_has_variable x (Q1535225_Var y) <=> x = y) /\
   (q1535225_term_has_variable x (Q1535225_Fun f arguments) <=>
      q1535225_term_list_has_variable x arguments) /\
   (q1535225_term_list_has_variable x [] <=> F) /\
   (q1535225_term_list_has_variable x (CONS term rest) <=>
      q1535225_term_has_variable x term \/
      q1535225_term_list_has_variable x rest)`;;

let q1535225_form_has_free_variable = new_recursive_definition
  q1535225_form_RECURSION
  `(q1535225_form_has_free_variable x (Q1535225_Equal left right) <=>
      q1535225_term_has_variable x left \/
      q1535225_term_has_variable x right) /\
   (q1535225_form_has_free_variable x
       (Q1535225_Rel relation arguments) <=>
      q1535225_term_list_has_variable x arguments) /\
   (q1535225_form_has_free_variable x (Q1535225_Not p) <=>
      q1535225_form_has_free_variable x p) /\
   (q1535225_form_has_free_variable x (Q1535225_And p q) <=>
      q1535225_form_has_free_variable x p \/
      q1535225_form_has_free_variable x q) /\
   (q1535225_form_has_free_variable x (Q1535225_Exists y p) <=>
      ~(x = y) /\ q1535225_form_has_free_variable x p)`;;

let q1535225_is_sentence = new_definition
  `q1535225_is_sentence p <=>
     !x. ~(q1535225_form_has_free_variable x p)`;;

let q1535225_update = new_definition
  `q1535225_update x a valuation =
     \y. if y = x then a else valuation y`;;

let q1535225_term_value = new_recursive_definition
  q1535225_term_RECURSION
  `(q1535225_term_value function_interpretation valuation
       (Q1535225_Var x) =
      valuation x) /\
   (q1535225_term_value function_interpretation valuation
       (Q1535225_Fun f arguments) =
      function_interpretation f
        (q1535225_term_list_value
           function_interpretation valuation arguments)) /\
   (q1535225_term_list_value function_interpretation valuation [] = []) /\
   (q1535225_term_list_value function_interpretation valuation
       (CONS term rest) =
      CONS (q1535225_term_value function_interpretation valuation term)
           (q1535225_term_list_value
              function_interpretation valuation rest))`;;

let q1535225_holds = new_recursive_definition
  q1535225_form_RECURSION
  `(q1535225_holds domain function_interpretation
       relation_interpretation valuation (Q1535225_Equal left right) <=>
      q1535225_term_value function_interpretation valuation left =
      q1535225_term_value function_interpretation valuation right) /\
   (q1535225_holds domain function_interpretation
       relation_interpretation valuation
       (Q1535225_Rel relation arguments) <=>
      relation_interpretation relation
        (q1535225_term_list_value
           function_interpretation valuation arguments)) /\
   (q1535225_holds domain function_interpretation
       relation_interpretation valuation (Q1535225_Not p) <=>
      ~(q1535225_holds domain function_interpretation
          relation_interpretation valuation p)) /\
   (q1535225_holds domain function_interpretation
       relation_interpretation valuation (Q1535225_And p q) <=>
      q1535225_holds domain function_interpretation
        relation_interpretation valuation p /\
      q1535225_holds domain function_interpretation
        relation_interpretation valuation q) /\
   (q1535225_holds domain function_interpretation
       relation_interpretation valuation (Q1535225_Exists x p) <=>
      ?a. domain a /\
          q1535225_holds domain function_interpretation
            relation_interpretation
            (q1535225_update x a valuation) p)`;;

let q1535225_is_ultrafilter = new_definition
  `q1535225_is_ultrafilter (u:(I->bool)->bool) <=>
     u (:I) /\
     ~(u {}) /\
     (!s t:I->bool. u s /\ u t ==> u (s INTER t)) /\
     (!s t:I->bool. u s /\ s SUBSET t ==> u t) /\
     (!s:I->bool. u s \/ u ((:I) DIFF s))`;;

let q1535225_is_structure = new_definition
  `q1535225_is_structure domain function_arity function_interpretation <=>
     (!f arguments.
        LENGTH arguments = function_arity f /\
        ALL domain arguments
        ==> domain (function_interpretation f arguments))`;;

let q1535225_choice_function = new_definition
  `q1535225_choice_function domain (choice:I->A) <=>
     !i. domain i (choice i)`;;

let q1535225_equivalent = new_definition
  `q1535225_equivalent u (left:I->A) right <=>
     u {i | left i = right i}`;;

let q1535225_class = new_definition
  `q1535225_class u domain (choice:I->A) =
     {other |
        q1535225_choice_function domain other /\
        q1535225_equivalent u choice other}`;;

let q1535225_representative = new_definition
  `q1535225_representative (class:(I->A)->bool) =
     @choice. choice IN class`;;

let q1535225_ultraproduct_carrier = new_definition
  `q1535225_ultraproduct_carrier u domain =
     IMAGE (q1535225_class u domain)
       {choice | q1535225_choice_function domain choice}`;;

let q1535225_ultraproduct_function = new_definition
  `q1535225_ultraproduct_function
       u domain function_interpretation f classes =
     q1535225_class u domain
       (\i.
          function_interpretation i f
            (MAP (\class. q1535225_representative class i) classes))`;;

let q1535225_ultraproduct_relation = new_definition
  `q1535225_ultraproduct_relation
       u relation_interpretation relation classes <=>
     u {i |
          relation_interpretation i relation
            (MAP (\class. q1535225_representative class i) classes)}`;;

let q1535225_sentence_holds = new_definition
  `q1535225_sentence_holds domain function_interpretation
       relation_interpretation p <=>
     !valuation.
       (!x. domain (valuation x))
       ==> q1535225_holds domain function_interpretation
             relation_interpretation valuation p`;;

let Q1535225_LOS_THEOREM =
 `!u:(I->bool)->bool.
  !domain:I->A->bool.
  !function_arity:F->num.
  !relation_arity:R->num.
  !function_interpretation:I->F->A list->A.
  !relation_interpretation:I->R->A list->bool.
  !p:(F,R)q1535225_form.
    q1535225_is_ultrafilter u /\
    (!i. ?a. domain i a) /\
    (!i. q1535225_is_structure
           (domain i) function_arity (function_interpretation i)) /\
    q1535225_form_wellformed function_arity relation_arity p /\
    q1535225_is_sentence p
    ==> (q1535225_sentence_holds
           (q1535225_ultraproduct_carrier u domain)
           (q1535225_ultraproduct_function
              u domain function_interpretation)
           (q1535225_ultraproduct_relation u relation_interpretation)
           p <=>
         u {i |
            q1535225_sentence_holds
              (domain i) (function_interpretation i)
              (relation_interpretation i) p})`;;
