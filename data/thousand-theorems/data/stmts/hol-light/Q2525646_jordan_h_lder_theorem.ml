(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2525646,
  "Jordan–Hölder theorem": two finite composition series with the same least
  and greatest elements in a Jordan-Hölder lattice have equivalent adjacent
  factors up to a bijection. This file contains no proof.
*)

let Q2525646_JORDAN_HOLDER_THEOREM =
  `let is_lattice =
     \(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A).
       (!x. le_rel x x) /\
       (!x y z. le_rel x y /\ le_rel y z ==> le_rel x z) /\
       (!x y. le_rel x y /\ le_rel y x ==> x = y) /\
       (!x y.
          le_rel (inf_op x y) x /\
          le_rel (inf_op x y) y /\
          (!z. le_rel z x /\ le_rel z y ==> le_rel z (inf_op x y))) /\
       (!x y.
          le_rel x (sup_op x y) /\
          le_rel y (sup_op x y) /\
          (!z. le_rel x z /\ le_rel y z ==> le_rel (sup_op x y) z)) in
   let jordan_holder_lattice =
     \(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A)
      (is_maximal:A->A->bool) (iso:(A#A)->(A#A)->bool).
       is_lattice le_rel inf_op sup_op /\
       (!x y.
          is_maximal x y ==> le_rel x y /\ ~(x = y)) /\
       (!x y z.
          is_maximal x z /\ is_maximal y z /\ ~(x = y)
          ==> sup_op x y = z) /\
       (!x y.
          is_maximal x (sup_op x y) /\
          is_maximal y (sup_op x y)
          ==> is_maximal (inf_op x y) x) /\
       (!p q. iso p q ==> iso q p) /\
       (!p q r. iso p q /\ iso q r ==> iso p r) /\
       (!x y.
          is_maximal x (sup_op x y)
          ==> iso (x,sup_op x y) (inf_op x y,y)) in
   let composition_series =
     \(is_maximal:A->A->bool) (n:num) (s:num->A).
       !i. i < n ==> is_maximal (s i) (s (SUC i)) in
   let equivalent_series =
     \(iso:(A#A)->(A#A)->bool)
      (n:num) (s:num->A) (m:num) (t:num->A).
       ?f:num->num.
         (!i. i < n ==> f i < m) /\
         (!i j. i < n /\ j < n /\ f i = f j ==> i = j) /\
         (!j. j < m ==> ?i. i < n /\ f i = j) /\
         (!i.
            i < n
            ==> iso (s i,s (SUC i))
                    (t (f i),t (SUC (f i)))) in
   !(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A)
    (is_maximal:A->A->bool) (iso:(A#A)->(A#A)->bool)
    (n:num) (s:num->A) (m:num) (t:num->A).
      jordan_holder_lattice
        le_rel inf_op sup_op is_maximal iso /\
      composition_series is_maximal n s /\
      composition_series is_maximal m t /\
      s 0 = t 0 /\
      s n = t m
      ==> equivalent_series iso n s m t`;;
