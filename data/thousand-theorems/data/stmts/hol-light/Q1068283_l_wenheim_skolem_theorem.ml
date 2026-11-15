(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1068283,
  "Löwenheim–Skolem theorem": for an infinite structure and an infinite
  cardinal at least as large as its first-order language, there is a structure
  of that cardinality with an elementary embedding in one direction between
  the two structures. This file contains no proof.
*)

let lowenheim_skolem_output = open_out "/dev/null";;
Format.pp_set_formatter_out_channel
  Format.std_formatter lowenheim_skolem_output;;

let Q1068283_LOWENHEIM_SKOLEM_THEOREM =
 `let is_structure_A =
    \(function_symbols:F->bool) (relation_symbols:R->bool)
     (function_arity:F->num) (relation_arity:R->num)
     (function_interp:F->(num->A)->A)
     (relation_interp:R->(num->A)->bool).
       (!f:F. !xs ys:num->A.
          f IN function_symbols /\
          (!i:num. i < function_arity f ==> xs i = ys i)
          ==> function_interp f xs = function_interp f ys) /\
       (!r:R. !xs ys:num->A.
          r IN relation_symbols /\
          (!i:num. i < relation_arity r ==> xs i = ys i)
          ==> (relation_interp r xs <=> relation_interp r ys)) in
  let is_structure_K =
    \(carrier_K:K->bool)
     (function_symbols:F->bool) (relation_symbols:R->bool)
     (function_arity:F->num) (relation_arity:R->num)
     (function_interp:F->(num->K)->K)
     (relation_interp:R->(num->K)->bool).
       (?x:K. x IN carrier_K) /\
       (!f:F. !xs:num->K.
          f IN function_symbols /\
          (!i:num. i < function_arity f ==> xs i IN carrier_K)
          ==> function_interp f xs IN carrier_K) /\
       (!f:F. !xs ys:num->K.
          f IN function_symbols /\
          (!i:num.
             i < function_arity f
             ==> xs i IN carrier_K /\
                 ys i IN carrier_K /\
                 xs i = ys i)
          ==> function_interp f xs = function_interp f ys) /\
       (!r:R. !xs ys:num->K.
          r IN relation_symbols /\
          (!i:num.
             i < relation_arity r
             ==> xs i IN carrier_K /\
                 ys i IN carrier_K /\
                 xs i = ys i)
          ==> (relation_interp r xs <=> relation_interp r ys)) in
  let carrier_card_eq_K =
    \(carrier_K:K->bool).
       ?enumerate:K->K.
         (!x:K. enumerate x IN carrier_K) /\
         (!x y:K. enumerate x = enumerate y ==> x = y) /\
         (!y:K. y IN carrier_K ==> ?x:K. enumerate x = y) in
  let language_card_le_K =
    \(function_symbols:F->bool) (relation_symbols:R->bool).
       ?code_num:num->K. ?code_function:F->K. ?code_relation:R->K.
         (!m n:num. code_num m = code_num n ==> m = n) /\
         (!f g:F.
            f IN function_symbols /\ g IN function_symbols /\
            code_function f = code_function g
            ==> f = g) /\
         (!r s:R.
            r IN relation_symbols /\ s IN relation_symbols /\
            code_relation r = code_relation s
            ==> r = s) /\
         (!n:num. !f:F.
            f IN function_symbols
            ==> ~(code_num n = code_function f)) /\
         (!n:num. !r:R.
            r IN relation_symbols
            ==> ~(code_num n = code_relation r)) /\
         (!f:F. !r:R.
            f IN function_symbols /\ r IN relation_symbols
            ==> ~(code_function f = code_relation r)) in
  let term_pair_AK =
    \(function_symbols:F->bool) (function_arity:F->num)
     (function_interp_A:F->(num->A)->A)
     (function_interp_K:F->(num->K)->K)
     (term_A:(num->A)->A) (term_K:(num->K)->K).
       !closed:((num->A)->A)->((num->K)->K)->bool.
         ((!j:num.
             closed (\assignment:num->A. assignment j)
                    (\assignment:num->K. assignment j)) /\
          (!f:F.
           !arguments_A:num->(num->A)->A.
           !arguments_K:num->(num->K)->K.
             f IN function_symbols /\
             (!i:num.
                i < function_arity f
                ==> closed (arguments_A i) (arguments_K i))
             ==> closed
                   (\assignment:num->A.
                      function_interp_A f
                        (\i:num. arguments_A i assignment))
                   (\assignment:num->K.
                      function_interp_K f
                        (\i:num. arguments_K i assignment))))
         ==> closed term_A term_K in
  let term_pair_KA =
    \(function_symbols:F->bool) (function_arity:F->num)
     (function_interp_K:F->(num->K)->K)
     (function_interp_A:F->(num->A)->A)
     (term_K:(num->K)->K) (term_A:(num->A)->A).
       !closed:((num->K)->K)->((num->A)->A)->bool.
         ((!j:num.
             closed (\assignment:num->K. assignment j)
                    (\assignment:num->A. assignment j)) /\
          (!f:F.
           !arguments_K:num->(num->K)->K.
           !arguments_A:num->(num->A)->A.
             f IN function_symbols /\
             (!i:num.
                i < function_arity f
                ==> closed (arguments_K i) (arguments_A i))
             ==> closed
                   (\assignment:num->K.
                      function_interp_K f
                        (\i:num. arguments_K i assignment))
                   (\assignment:num->A.
                      function_interp_A f
                        (\i:num. arguments_A i assignment))))
         ==> closed term_K term_A in
  let formula_pair_AK =
    \(carrier_K:K->bool)
     (function_symbols:F->bool) (relation_symbols:R->bool)
     (function_arity:F->num) (relation_arity:R->num)
     (function_interp_A:F->(num->A)->A)
     (relation_interp_A:R->(num->A)->bool)
     (function_interp_K:F->(num->K)->K)
     (relation_interp_K:R->(num->K)->bool)
     (formula_A:(num->A)->bool) (formula_K:(num->K)->bool).
       !closed:((num->A)->bool)->((num->K)->bool)->bool.
         ((!left_A right_A:(num->A)->A.
           !left_K right_K:(num->K)->K.
             term_pair_AK function_symbols function_arity
               function_interp_A function_interp_K left_A left_K /\
             term_pair_AK function_symbols function_arity
               function_interp_A function_interp_K right_A right_K
             ==> closed
                   (\assignment:num->A.
                      left_A assignment = right_A assignment)
                   (\assignment:num->K.
                      left_K assignment = right_K assignment)) /\
          (!r:R.
           !arguments_A:num->(num->A)->A.
           !arguments_K:num->(num->K)->K.
             r IN relation_symbols /\
             (!i:num.
                i < relation_arity r
                ==> term_pair_AK function_symbols function_arity
                      function_interp_A function_interp_K
                      (arguments_A i) (arguments_K i))
             ==> closed
                   (\assignment:num->A.
                      relation_interp_A r
                        (\i:num. arguments_A i assignment))
                   (\assignment:num->K.
                      relation_interp_K r
                        (\i:num. arguments_K i assignment))) /\
          (!p_A:(num->A)->bool. !p_K:(num->K)->bool.
             closed p_A p_K
             ==> closed
                   (\assignment:num->A. ~(p_A assignment))
                   (\assignment:num->K. ~(p_K assignment))) /\
          (!p_A q_A:(num->A)->bool.
           !p_K q_K:(num->K)->bool.
             closed p_A p_K /\ closed q_A q_K
             ==> closed
                   (\assignment:num->A.
                      p_A assignment /\ q_A assignment)
                   (\assignment:num->K.
                      p_K assignment /\ q_K assignment)) /\
          (!p_A:(num->A)->bool. !p_K:(num->K)->bool.
             closed p_A p_K
             ==> closed
                   (\assignment:num->A.
                      ?x:A.
                        p_A
                          (\i:num.
                             if i = 0 then x
                             else assignment (PRE i)))
                   (\assignment:num->K.
                      ?x:K.
                        x IN carrier_K /\
                        p_K
                          (\i:num.
                             if i = 0 then x
                             else assignment (PRE i)))))
         ==> closed formula_A formula_K in
  let formula_pair_KA =
    \(carrier_K:K->bool)
     (function_symbols:F->bool) (relation_symbols:R->bool)
     (function_arity:F->num) (relation_arity:R->num)
     (function_interp_K:F->(num->K)->K)
     (relation_interp_K:R->(num->K)->bool)
     (function_interp_A:F->(num->A)->A)
     (relation_interp_A:R->(num->A)->bool)
     (formula_K:(num->K)->bool) (formula_A:(num->A)->bool).
       !closed:((num->K)->bool)->((num->A)->bool)->bool.
         ((!left_K right_K:(num->K)->K.
           !left_A right_A:(num->A)->A.
             term_pair_KA function_symbols function_arity
               function_interp_K function_interp_A left_K left_A /\
             term_pair_KA function_symbols function_arity
               function_interp_K function_interp_A right_K right_A
             ==> closed
                   (\assignment:num->K.
                      left_K assignment = right_K assignment)
                   (\assignment:num->A.
                      left_A assignment = right_A assignment)) /\
          (!r:R.
           !arguments_K:num->(num->K)->K.
           !arguments_A:num->(num->A)->A.
             r IN relation_symbols /\
             (!i:num.
                i < relation_arity r
                ==> term_pair_KA function_symbols function_arity
                      function_interp_K function_interp_A
                      (arguments_K i) (arguments_A i))
             ==> closed
                   (\assignment:num->K.
                      relation_interp_K r
                        (\i:num. arguments_K i assignment))
                   (\assignment:num->A.
                      relation_interp_A r
                        (\i:num. arguments_A i assignment))) /\
          (!p_K:(num->K)->bool. !p_A:(num->A)->bool.
             closed p_K p_A
             ==> closed
                   (\assignment:num->K. ~(p_K assignment))
                   (\assignment:num->A. ~(p_A assignment))) /\
          (!p_K q_K:(num->K)->bool.
           !p_A q_A:(num->A)->bool.
             closed p_K p_A /\ closed q_K q_A
             ==> closed
                   (\assignment:num->K.
                      p_K assignment /\ q_K assignment)
                   (\assignment:num->A.
                      p_A assignment /\ q_A assignment)) /\
          (!p_K:(num->K)->bool. !p_A:(num->A)->bool.
             closed p_K p_A
             ==> closed
                   (\assignment:num->K.
                      ?x:K.
                        x IN carrier_K /\
                        p_K
                          (\i:num.
                             if i = 0 then x
                             else assignment (PRE i)))
                   (\assignment:num->A.
                      ?x:A.
                        p_A
                          (\i:num.
                             if i = 0 then x
                             else assignment (PRE i)))))
         ==> closed formula_K formula_A in
  let elementary_AK =
    \(carrier_K:K->bool)
     (function_symbols:F->bool) (relation_symbols:R->bool)
     (function_arity:F->num) (relation_arity:R->num)
     (function_interp_A:F->(num->A)->A)
     (relation_interp_A:R->(num->A)->bool)
     (function_interp_K:F->(num->K)->K)
     (relation_interp_K:R->(num->K)->bool)
     (embedding:A->K).
       (!x:A. embedding x IN carrier_K) /\
       (!x y:A. embedding x = embedding y ==> x = y) /\
       (!f:F. !arguments:num->A.
          f IN function_symbols
          ==> embedding (function_interp_A f arguments) =
              function_interp_K f
                (\i:num. embedding (arguments i))) /\
       (!r:R. !arguments:num->A.
          r IN relation_symbols
          ==> (relation_interp_A r arguments <=>
               relation_interp_K r
                 (\i:num. embedding (arguments i)))) /\
       (!formula_A:(num->A)->bool.
        !formula_K:(num->K)->bool.
          formula_pair_AK
            carrier_K
            function_symbols relation_symbols
            function_arity relation_arity
            function_interp_A relation_interp_A
            function_interp_K relation_interp_K
            formula_A formula_K
          ==> !assignment:num->A.
                (formula_A assignment <=>
                 formula_K
                   (\i:num. embedding (assignment i)))) in
  let elementary_KA =
    \(carrier_K:K->bool)
     (function_symbols:F->bool) (relation_symbols:R->bool)
     (function_arity:F->num) (relation_arity:R->num)
     (function_interp_K:F->(num->K)->K)
     (relation_interp_K:R->(num->K)->bool)
     (function_interp_A:F->(num->A)->A)
     (relation_interp_A:R->(num->A)->bool)
     (embedding:K->A).
       (!x y:K.
          x IN carrier_K /\ y IN carrier_K /\
          embedding x = embedding y
          ==> x = y) /\
       (!f:F. !arguments:num->K.
          f IN function_symbols /\
          (!i:num.
             i < function_arity f ==> arguments i IN carrier_K)
          ==> embedding (function_interp_K f arguments) =
              function_interp_A f
                (\i:num. embedding (arguments i))) /\
       (!r:R. !arguments:num->K.
          r IN relation_symbols /\
          (!i:num.
             i < relation_arity r ==> arguments i IN carrier_K)
          ==> (relation_interp_K r arguments <=>
               relation_interp_A r
                 (\i:num. embedding (arguments i)))) /\
       (!formula_K:(num->K)->bool.
        !formula_A:(num->A)->bool.
          formula_pair_KA
            carrier_K
            function_symbols relation_symbols
            function_arity relation_arity
            function_interp_K relation_interp_K
            function_interp_A relation_interp_A
            formula_K formula_A
          ==> !assignment:num->K.
                (!i:num. assignment i IN carrier_K)
                ==>
                (formula_K assignment <=>
                 formula_A
                   (\i:num. embedding (assignment i)))) in
  !function_symbols:F->bool.
  !relation_symbols:R->bool.
  !function_arity:F->num.
  !relation_arity:R->num.
  !function_interp_A:F->(num->A)->A.
  !relation_interp_A:R->(num->A)->bool.
    is_structure_A
      function_symbols relation_symbols
      function_arity relation_arity
      function_interp_A relation_interp_A /\
    (?enumerate:num->A.
       !m n:num. enumerate m = enumerate n ==> m = n) /\
    language_card_le_K function_symbols relation_symbols
    ==> ?carrier_K:K->bool.
        ?function_interp_K:F->(num->K)->K.
        ?relation_interp_K:R->(num->K)->bool.
          is_structure_K
            carrier_K
            function_symbols relation_symbols
            function_arity relation_arity
            function_interp_K relation_interp_K /\
          carrier_card_eq_K carrier_K /\
          ((?embedding:K->A.
              elementary_KA
                carrier_K
                function_symbols relation_symbols
                function_arity relation_arity
                function_interp_K relation_interp_K
                function_interp_A relation_interp_A
                embedding) \/
           (?embedding:A->K.
              elementary_AK
                carrier_K
                function_symbols relation_symbols
                function_arity relation_arity
                function_interp_A relation_interp_A
                function_interp_K relation_interp_K
                embedding))`;;

Format.pp_print_flush Format.std_formatter ();;
Format.pp_set_formatter_out_channel Format.std_formatter stdout;;
close_out lowenheim_skolem_output;;
