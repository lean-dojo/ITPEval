(*
  Statement-only formalization of Thousand Theorems corpus artifact Q574902
  (thousand-theorems__hol-light__Q574902), "Tarski's indefinability theorem":
  no one-variable first-order arithmetic formula defines truth for every
  arithmetic sentence in the standard natural-number model when instantiated
  with that sentence's Godel code. This file contains no proof.
*)

let q574902_term_INDUCT,q574902_term_RECURSION = define_type
  "q574902_term =
       Q574902_Var num
     | Q574902_Zero
     | Q574902_One
     | Q574902_Add q574902_term q574902_term
     | Q574902_Mul q574902_term q574902_term";;

let q574902_form_INDUCT,q574902_form_RECURSION = define_type
  "q574902_form =
       Q574902_True
     | Q574902_False
     | Q574902_Equal q574902_term q574902_term
     | Q574902_NotEqual q574902_term q574902_term
     | Q574902_Less q574902_term q574902_term
     | Q574902_NotLess q574902_term q574902_term
     | Q574902_And q574902_form q574902_form
     | Q574902_Or q574902_form q574902_form
     | Q574902_Forall q574902_form
     | Q574902_Exists q574902_form";;

let q574902_term_wellscoped = new_recursive_definition
  q574902_term_RECURSION
  `(q574902_term_wellscoped depth (Q574902_Var i) <=> i < depth) /\
   (q574902_term_wellscoped depth Q574902_Zero <=> T) /\
   (q574902_term_wellscoped depth Q574902_One <=> T) /\
   (q574902_term_wellscoped depth (Q574902_Add s t) <=>
      q574902_term_wellscoped depth s /\
      q574902_term_wellscoped depth t) /\
   (q574902_term_wellscoped depth (Q574902_Mul s t) <=>
      q574902_term_wellscoped depth s /\
      q574902_term_wellscoped depth t)`;;

let q574902_form_wellscoped = new_recursive_definition
  q574902_form_RECURSION
  `(q574902_form_wellscoped depth Q574902_True <=> T) /\
   (q574902_form_wellscoped depth Q574902_False <=> T) /\
   (q574902_form_wellscoped depth (Q574902_Equal s t) <=>
      q574902_term_wellscoped depth s /\
      q574902_term_wellscoped depth t) /\
   (q574902_form_wellscoped depth (Q574902_NotEqual s t) <=>
      q574902_term_wellscoped depth s /\
      q574902_term_wellscoped depth t) /\
   (q574902_form_wellscoped depth (Q574902_Less s t) <=>
      q574902_term_wellscoped depth s /\
      q574902_term_wellscoped depth t) /\
   (q574902_form_wellscoped depth (Q574902_NotLess s t) <=>
      q574902_term_wellscoped depth s /\
      q574902_term_wellscoped depth t) /\
   (q574902_form_wellscoped depth (Q574902_And p q) <=>
      q574902_form_wellscoped depth p /\
      q574902_form_wellscoped depth q) /\
   (q574902_form_wellscoped depth (Q574902_Or p q) <=>
      q574902_form_wellscoped depth p /\
      q574902_form_wellscoped depth q) /\
   (q574902_form_wellscoped depth (Q574902_Forall p) <=>
      q574902_form_wellscoped (SUC depth) p) /\
   (q574902_form_wellscoped depth (Q574902_Exists p) <=>
      q574902_form_wellscoped (SUC depth) p)`;;

let q574902_numeral = new_recursive_definition num_RECURSION
  `(q574902_numeral 0 = Q574902_Zero) /\
   (q574902_numeral (SUC n) =
      Q574902_Add (q574902_numeral n) Q574902_One)`;;

let q574902_term_subst = new_recursive_definition
  q574902_term_RECURSION
  `(q574902_term_subst variable n (Q574902_Var i) =
      if i = variable then q574902_numeral n
      else if variable < i then Q574902_Var (PRE i)
      else Q574902_Var i) /\
   (q574902_term_subst variable n Q574902_Zero = Q574902_Zero) /\
   (q574902_term_subst variable n Q574902_One = Q574902_One) /\
   (q574902_term_subst variable n (Q574902_Add s t) =
      Q574902_Add
        (q574902_term_subst variable n s)
        (q574902_term_subst variable n t)) /\
   (q574902_term_subst variable n (Q574902_Mul s t) =
      Q574902_Mul
        (q574902_term_subst variable n s)
        (q574902_term_subst variable n t))`;;

let q574902_form_subst = new_recursive_definition
  q574902_form_RECURSION
  `(q574902_form_subst variable n Q574902_True = Q574902_True) /\
   (q574902_form_subst variable n Q574902_False = Q574902_False) /\
   (q574902_form_subst variable n (Q574902_Equal s t) =
      Q574902_Equal
        (q574902_term_subst variable n s)
        (q574902_term_subst variable n t)) /\
   (q574902_form_subst variable n (Q574902_NotEqual s t) =
      Q574902_NotEqual
        (q574902_term_subst variable n s)
        (q574902_term_subst variable n t)) /\
   (q574902_form_subst variable n (Q574902_Less s t) =
      Q574902_Less
        (q574902_term_subst variable n s)
        (q574902_term_subst variable n t)) /\
   (q574902_form_subst variable n (Q574902_NotLess s t) =
      Q574902_NotLess
        (q574902_term_subst variable n s)
        (q574902_term_subst variable n t)) /\
   (q574902_form_subst variable n (Q574902_And p q) =
      Q574902_And
        (q574902_form_subst variable n p)
        (q574902_form_subst variable n q)) /\
   (q574902_form_subst variable n (Q574902_Or p q) =
      Q574902_Or
        (q574902_form_subst variable n p)
        (q574902_form_subst variable n q)) /\
   (q574902_form_subst variable n (Q574902_Forall p) =
      Q574902_Forall (q574902_form_subst (SUC variable) n p)) /\
   (q574902_form_subst variable n (Q574902_Exists p) =
      Q574902_Exists (q574902_form_subst (SUC variable) n p))`;;

let q574902_pair = new_definition
  `q574902_pair a b =
     ((a + b) * (a + b + 1)) DIV 2 + b`;;

let q574902_term_code = new_recursive_definition
  q574902_term_RECURSION
  `(q574902_term_code (Q574902_Var i) = q574902_pair 0 i) /\
   (q574902_term_code Q574902_Zero = q574902_pair 1 0) /\
   (q574902_term_code Q574902_One = q574902_pair 2 0) /\
   (q574902_term_code (Q574902_Add s t) =
      q574902_pair 3
        (q574902_pair (q574902_term_code s) (q574902_term_code t))) /\
   (q574902_term_code (Q574902_Mul s t) =
      q574902_pair 4
        (q574902_pair (q574902_term_code s) (q574902_term_code t)))`;;

let q574902_form_code = new_recursive_definition
  q574902_form_RECURSION
  `(q574902_form_code Q574902_True = q574902_pair 0 0) /\
   (q574902_form_code Q574902_False = q574902_pair 1 0) /\
   (q574902_form_code (Q574902_Equal s t) =
      q574902_pair 2
        (q574902_pair (q574902_term_code s) (q574902_term_code t))) /\
   (q574902_form_code (Q574902_NotEqual s t) =
      q574902_pair 3
        (q574902_pair (q574902_term_code s) (q574902_term_code t))) /\
   (q574902_form_code (Q574902_Less s t) =
      q574902_pair 4
        (q574902_pair (q574902_term_code s) (q574902_term_code t))) /\
   (q574902_form_code (Q574902_NotLess s t) =
      q574902_pair 5
        (q574902_pair (q574902_term_code s) (q574902_term_code t))) /\
   (q574902_form_code (Q574902_And p q) =
      q574902_pair 6
        (q574902_pair (q574902_form_code p) (q574902_form_code q))) /\
   (q574902_form_code (Q574902_Or p q) =
      q574902_pair 7
        (q574902_pair (q574902_form_code p) (q574902_form_code q))) /\
   (q574902_form_code (Q574902_Forall p) =
      q574902_pair 8 (q574902_form_code p)) /\
   (q574902_form_code (Q574902_Exists p) =
      q574902_pair 9 (q574902_form_code p))`;;

let q574902_term_value = new_recursive_definition
  q574902_term_RECURSION
  `(q574902_term_value valuation (Q574902_Var i) = valuation i) /\
   (q574902_term_value valuation Q574902_Zero = 0) /\
   (q574902_term_value valuation Q574902_One = 1) /\
   (q574902_term_value valuation (Q574902_Add s t) =
      q574902_term_value valuation s +
      q574902_term_value valuation t) /\
   (q574902_term_value valuation (Q574902_Mul s t) =
      q574902_term_value valuation s *
      q574902_term_value valuation t)`;;

let q574902_holds = new_recursive_definition
  q574902_form_RECURSION
  `(q574902_holds valuation Q574902_True <=> T) /\
   (q574902_holds valuation Q574902_False <=> F) /\
   (q574902_holds valuation (Q574902_Equal s t) <=>
      q574902_term_value valuation s = q574902_term_value valuation t) /\
   (q574902_holds valuation (Q574902_NotEqual s t) <=>
      ~(q574902_term_value valuation s =
        q574902_term_value valuation t)) /\
   (q574902_holds valuation (Q574902_Less s t) <=>
      q574902_term_value valuation s < q574902_term_value valuation t) /\
   (q574902_holds valuation (Q574902_NotLess s t) <=>
      ~(q574902_term_value valuation s <
        q574902_term_value valuation t)) /\
   (q574902_holds valuation (Q574902_And p q) <=>
      q574902_holds valuation p /\ q574902_holds valuation q) /\
   (q574902_holds valuation (Q574902_Or p q) <=>
      q574902_holds valuation p \/ q574902_holds valuation q) /\
   (q574902_holds valuation (Q574902_Forall p) <=>
      !x:num.
        q574902_holds
          (\i. if i = 0 then x else valuation (PRE i)) p) /\
   (q574902_holds valuation (Q574902_Exists p) <=>
      ?x:num.
        q574902_holds
          (\i. if i = 0 then x else valuation (PRE i)) p)`;;

let q574902_standard_truth = new_definition
  `q574902_standard_truth p <=>
     q574902_holds (\i:num. 0) p`;;

let Q574902_TARSKIS_INDEFINABILITY_THEOREM =
  `~(?tau:q574902_form.
       q574902_form_wellscoped 1 tau /\
       !sigma:q574902_form.
         q574902_form_wellscoped 0 sigma
         ==> (q574902_standard_truth sigma <=>
              q574902_standard_truth
                (q574902_form_subst
                  0 (q574902_form_code sigma) tau)))`;;
