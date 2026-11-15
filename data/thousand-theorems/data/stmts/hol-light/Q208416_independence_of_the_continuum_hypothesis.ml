(*
  Statement-only formalization of Thousand Theorems corpus artifact Q208416,
  "Independence of the continuum hypothesis": ZFC has a countable model
  satisfying the continuum hypothesis and a countable model satisfying its
  negation, equivalently neither CH nor its negation is provable in ZFC.
  This file contains no proof.
*)

needs "Logic/fol.ml";;

let Q208416_INDEPENDENCE_OF_THE_CONTINUUM_HYPOTHESIS =
  `let interp =
     \(member:num->num->bool).
       (UNIV:num->bool,
        (\(f:num) (args:num list). @x:num. T),
        (\(p:num) (args:num list).
           (p = 0 /\ ?x y:num. args = [x; y] /\ x = y) \/
           (p = 1 /\ ?x y:num. args = [x; y] /\ member x y))) in
   let set_formula =
     \p:form.
       functions_form p = {} /\
       predicates_form p SUBSET {(0,2),(1,2)} in
   let empty_set =
     \(member:num->num->bool) (e:num).
       !x:num. ~(member x e) in
   let pair_set =
     \(member:num->num->bool) (x:num) (y:num) (p:num).
       !z:num. member z p <=> z = x \/ z = y in
   let union_set =
     \(member:num->num->bool) (x:num) (u:num).
       !z:num. member z u <=> ?y:num. member y x /\ member z y in
   let powerset =
     \(member:num->num->bool) (x:num) (p:num).
       !z:num. member z p <=> !y:num. member y z ==> member y x in
   let successor_set =
     \(member:num->num->bool) (x:num) (s:num).
       !z:num. member z s <=> member z x \/ z = x in
   let inductive_set =
     \(member:num->num->bool) (i:num).
       (?e:num. empty_set member e /\ member e i) /\
       (!x:num.
          member x i
          ==> ?s:num. successor_set member x s /\ member s i) in
   let is_omega =
     \(member:num->num->bool) (w:num).
       inductive_set member w /\
       !i:num.
         inductive_set member i
         ==> !x:num. member x w ==> member x i in
   let is_ordinal =
     \(member:num->num->bool) (a:num).
       (!x y:num. member x a /\ member y x ==> member y a) /\
       (!x:num. member x a ==> ~(member x x)) /\
       (!x y z:num.
          member x a /\ member y a /\ member z a /\
          member x y /\ member y z
          ==> member x z) /\
       (!x y:num.
          member x a /\ member y a
          ==> member x y \/ x = y \/ member y x) /\
       (!s:num.
          (!x:num. member x s ==> member x a) /\
          (?x:num. member x s)
          ==> ?x:num.
                member x s /\
                !y:num. member y s ==> y = x \/ member x y) in
   let unordered_pair =
     \(member:num->num->bool) (x:num) (y:num) (u:num).
       !z:num. member z u <=> z = x \/ z = y in
   let ordered_pair =
     \(member:num->num->bool) (x:num) (y:num) (p:num).
       ?u v:num.
         unordered_pair member x x u /\
         unordered_pair member x y v /\
         unordered_pair member u v p in
   let relates =
     \(member:num->num->bool) (r:num) (x:num) (y:num).
       ?p:num. member p r /\ ordered_pair member x y p in
   let is_function =
     \(member:num->num->bool) (f:num) (a:num) (b:num).
       (!p:num.
          member p f
          ==> ?x y:num.
                member x a /\ member y b /\
                ordered_pair member x y p) /\
       (!x:num.
          member x a
          ==> ?y:num.
                member y b /\ relates member f x y /\
                !y':num.
                  member y' b /\ relates member f x y'
                  ==> y' = y) in
   let is_injection =
     \(member:num->num->bool) (f:num) (a:num) (b:num).
       is_function member f a b /\
       !x x' y:num.
         member x a /\ member x' a /\ member y b /\
         relates member f x y /\ relates member f x' y
         ==> x = x' in
   let is_surjection =
     \(member:num->num->bool) (f:num) (a:num) (b:num).
       is_function member f a b /\
       !y:num.
         member y b
         ==> ?x:num. member x a /\ relates member f x y in
   let is_bijection =
     \(member:num->num->bool) (f:num) (a:num) (b:num).
       is_injection member f a b /\ is_surjection member f a b in
   let zf_model =
     \(member:num->num->bool).
       (!x y:num.
          (!z:num. member z x <=> member z y)
          ==> x = y) /\
       (?e:num. empty_set member e) /\
       (!x y:num. ?p:num. pair_set member x y p) /\
       (!x:num. ?u:num. union_set member x u) /\
       (!x:num. ?p:num. powerset member x p) /\
       (?i:num. inductive_set member i) /\
       (!x:num.
          (?y:num. member y x)
          ==> ?y:num.
                member y x /\
                !z:num. member z x ==> ~(member z y)) /\
       (!p:form v:num->num a:num.
          set_formula p /\ valuation (interp member) v
          ==> ?b:num.
                !x:num.
                  member x b <=>
                  member x a /\
                  holds (interp member) (valmod (0,x) v) p) /\
       (!p:form v:num->num a:num.
          set_formula p /\ valuation (interp member) v /\
          (!x:num.
             member x a
             ==> ?y:num.
                   holds (interp member)
                     (valmod (1,y) (valmod (0,x) v)) p /\
                   !y':num.
                     holds (interp member)
                       (valmod (1,y') (valmod (0,x) v)) p
                     ==> y' = y)
          ==> ?b:num.
                !y:num.
                  member y b <=>
                  ?x:num.
                    member x a /\
                    holds (interp member)
                      (valmod (1,y) (valmod (0,x) v)) p) in
   let choice_model =
     \(member:num->num->bool).
       !x:num.
         ?a f:num.
           is_ordinal member a /\
           is_surjection member f a x in
   let zfc_model =
     \(member:num->num->bool).
       zf_model member /\ choice_model member in
   let continuum_hypothesis =
     \(member:num->num->bool).
       ?omega pomega:num.
         is_omega member omega /\
         powerset member omega pomega /\
         !x:num.
           (?f:num. is_injection member f omega x) /\
           (?g:num. is_injection member g x pomega)
           ==> (?h:num. is_bijection member h x omega) \/
               (?h:num. is_bijection member h x pomega) in
   (?member:num->num->bool.
      zfc_model member /\ continuum_hypothesis member) /\
   (?member:num->num->bool.
      zfc_model member /\ ~(continuum_hypothesis member))`;;
