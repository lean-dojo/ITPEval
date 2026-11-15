(*
  Statement-only formalization of Hundred Theorems artifact 024,
  "The Undecidability of the Continuum Hypothesis". It states the source's
  forcing result that every countable transitive model of ZF has a proper
  countable transitive ZF extension with the same ambient ordinals, where
  countability uses a set-coded bijection with ambient omega and internal
  choice is preserved as ZFC in the extension. This file contains no proof.
*)

needs "Logic/fol.ml";;

let EXTENSIONS_OF_CTMS =
  `!(member:A->A->bool).
     let interp =
       \D:A->bool.
         (D,
          (\(f:num) (args:A list). @x:A. T),
          (\(p:num) (args:A list).
             (p = 0 /\ ?x y:A. args = [x; y] /\ x = y) \/
             (p = 1 /\ ?x y:A. args = [x; y] /\ member x y))) in
     let set_formula =
       \p:form.
         functions_form p = {} /\
         predicates_form p SUBSET {(0,2),(1,2)} in
     let zf_model =
       \D:A->bool.
         (!x y:A.
            x IN D /\ y IN D /\
            (!z:A. z IN D ==> (member z x <=> member z y))
            ==> x = y) /\
         (?e:A. e IN D /\ !x:A. x IN D ==> ~(member x e)) /\
         (!x y:A.
            x IN D /\ y IN D
            ==> ?p:A.
                  p IN D /\
                  !z:A. z IN D
                        ==> (member z p <=> z = x \/ z = y)) /\
         (!x:A.
            x IN D
            ==> ?u:A.
                  u IN D /\
                  !z:A. z IN D
                        ==> (member z u <=>
                             ?y:A. y IN D /\ member y x /\ member z y)) /\
         (!x:A.
            x IN D
            ==> ?p:A.
                  p IN D /\
                  !z:A. z IN D
                        ==> (member z p <=>
                             !y:A.
                               y IN D /\ member y z ==> member y x)) /\
         (?i:A.
            i IN D /\
            (?e:A.
               e IN D /\
               (!z:A. z IN D ==> ~(member z e)) /\
               member e i) /\
            (!x:A.
               x IN D /\ member x i
               ==> ?s:A.
                     s IN D /\ member s i /\
                     !z:A.
                       z IN D
                       ==> (member z s <=> member z x \/ z = x))) /\
         (!x:A.
            x IN D /\ (?y:A. y IN D /\ member y x)
            ==> ?y:A.
                  y IN D /\ member y x /\
                  !z:A.
                    z IN D /\ member z x ==> ~(member z y)) /\
         (!p:form v:num->A a:A.
            set_formula p /\ valuation (interp D) v /\ a IN D
            ==> ?b:A.
                  b IN D /\
                  !x:A.
                    x IN D
                    ==> (member x b <=>
                         member x a /\
                         holds (interp D) (valmod (0,x) v) p)) /\
         (!p:form v:num->A a:A.
            set_formula p /\ valuation (interp D) v /\ a IN D /\
            (!x:A.
               x IN D /\ member x a
               ==> ?y:A.
                     y IN D /\
                     holds (interp D)
                       (valmod (1,y) (valmod (0,x) v)) p /\
                     !y':A.
                       y' IN D /\
                       holds (interp D)
                         (valmod (1,y') (valmod (0,x) v)) p
                       ==> y' = y)
            ==> ?b:A.
                  b IN D /\
                  !y:A.
                    y IN D
                    ==> (member y b <=>
                         ?x:A.
                           x IN D /\ member x a /\
                           holds (interp D)
                             (valmod (1,y) (valmod (0,x) v)) p)) in
     let transitive_set =
       \m:A.
         !x y:A. member x m /\ member y x ==> member y m in
     let empty_set =
       \D:A->bool e:A.
         e IN D /\
         !x:A. x IN D ==> ~(member x e) in
     let successor_set =
       \D:A->bool x:A s:A.
         s IN D /\
         !z:A.
           z IN D ==> (member z s <=> member z x \/ z = x) in
     let inductive_set =
       \D:A->bool i:A.
         i IN D /\
         (?e:A. empty_set D e /\ member e i) /\
         (!x:A.
            x IN D /\ member x i
            ==> ?s:A.
                  successor_set D x s /\ member s i) in
     let is_omega =
       \D:A->bool w:A.
         w IN D /\
         inductive_set D w /\
         !i:A.
           inductive_set D i
           ==> !x:A.
                 x IN D /\ member x w ==> member x i in
     let is_ordinal =
       \D:A->bool a:A.
         a IN D /\
         (!x y:A.
            x IN D /\ y IN D /\ member x a /\ member y x
            ==> member y a) /\
         (!x:A.
            x IN D /\ member x a ==> ~(member x x)) /\
         (!x y z:A.
            x IN D /\ y IN D /\ z IN D /\
            member x a /\ member y a /\ member z a /\
            member x y /\ member y z
            ==> member x z) /\
         (!x y:A.
            x IN D /\ y IN D /\ member x a /\ member y a
            ==> member x y \/ x = y \/ member y x) /\
         (!s:A.
            s IN D /\
            (!x:A.
               x IN D /\ member x s ==> member x a) /\
            (?x:A. x IN D /\ member x s)
            ==> ?x:A.
                  x IN D /\ member x s /\
                  !y:A.
                    y IN D /\ member y s
                    ==> y = x \/ member x y) in
     let upair =
       \D:A->bool x:A y:A u:A.
         u IN D /\
         !z:A. z IN D ==> (member z u <=> z = x \/ z = y) in
     let opair =
       \D:A->bool x:A y:A p:A.
         ?u v:A.
           upair D x x u /\
           upair D x y v /\
           upair D u v p in
     let relates =
       \D:A->bool r:A x:A y:A.
         ?p:A. p IN D /\ member p r /\ opair D x y p in
     let is_surjection =
       \D:A->bool f:A a:A b:A.
         f IN D /\ a IN D /\ b IN D /\
         (!p:A.
            p IN D /\ member p f
            ==> ?x y:A.
                  x IN D /\ y IN D /\
                  member x a /\ member y b /\
                  opair D x y p) /\
         (!x:A.
            x IN D /\ member x a
            ==> ?y:A.
                  y IN D /\ member y b /\ relates D f x y /\
                  !y':A.
                    y' IN D /\ member y' b /\ relates D f x y'
                    ==> y' = y) /\
         (!y:A.
            y IN D /\ member y b
            ==> ?x:A.
                  x IN D /\ member x a /\ relates D f x y) in
     let is_bijection =
       \D:A->bool f:A a:A b:A.
         is_surjection D f a b /\
         !x x' y:A.
           x IN D /\ x' IN D /\ y IN D /\
           member x a /\ member x' a /\ member y b /\
           relates D f x y /\ relates D f x' y
           ==> x = x' in
     let choice_model =
       \D:A->bool.
         !x:A.
           x IN D
           ==> ?a f:A.
                 a IN D /\ f IN D /\
                 is_ordinal D a /\ is_surjection D f a x in
     let zfc_model =
       \D:A->bool.
         zf_model D /\ choice_model D in
     let countably_infinite =
       \m:A.
         ?omega enum:A.
           is_omega (UNIV:A->bool) omega /\
           is_bijection (UNIV:A->bool) enum omega m in
     zf_model (UNIV:A->bool)
     ==> !M:A.
           countably_infinite M /\
           transitive_set M /\
           zf_model (\x:A. member x M)
           ==> ?N:A.
                 (!x:A. member x M ==> member x N) /\
                 countably_infinite N /\
                 transitive_set N /\
                 zf_model (\x:A. member x N) /\
                 ~(M = N) /\
                 (!a:A.
                    is_ordinal (UNIV:A->bool) a
                    ==> (member a M <=> member a N)) /\
                 (choice_model (\x:A. member x M)
                  ==> zfc_model (\x:A. member x N))`;;
