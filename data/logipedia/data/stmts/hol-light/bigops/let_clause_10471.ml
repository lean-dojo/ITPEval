(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.let_clause_10471, catalog title "bigops.let_clause_10471": a nested
  induction-step statement for predicate-filtered finite products, ending in
  the natural-number division and remainder identity. This file contains no
  proof.
*)

let logipedia_bigops_bigop = new_recursive_definition num_RECURSION
  `(logipedia_bigops_bigop
       0 (p:num->bool) (nil:A) (op:A->A->A) (f:num->A) = nil) /\
   (logipedia_bigops_bigop
       (SUC n) (p:num->bool) (nil:A) (op:A->A->A) (f:num->A) =
      if p n then
        op (f n) (logipedia_bigops_bigop n p nil op f)
      else
        logipedia_bigops_bigop n p nil op f)`;;

let logipedia_bigops_sub_hk = new_definition
  `logipedia_bigops_sub_hk
       (h:num->num) (k:num->num) (n1:num) (n2:num)
       (p1:num->bool) (p2:num->bool) (f1:num->num) (f2:num->num) <=>
     !i:num.
       i < n1
       ==>
       p1 i = T
       ==>
       (h i < n2 /\ p2 (h i) = T) /\ k (h i) = i`;;

let logipedia_bigops_iso = new_definition
  `logipedia_bigops_iso
       (n1:num) (n2:num) (p1:num->bool) (p2:num->bool)
       (f1:num->num) (f2:num->num) <=>
     ?h k:num->num.
       ((!i:num.
           i < n1
           ==>
           p1 i = T
           ==>
           f1 i = f2 (h i)) /\
        logipedia_bigops_sub_hk h k n1 n2 p1 p2 f1 f2) /\
       logipedia_bigops_sub_hk k h n2 n1 p2 p1 f2 f1`;;

let statement =
  `!n1 n2:num.
   !p1 p2:num->bool.
   !f1 f2:num->num.
     logipedia_bigops_iso n1 n2 p1 p2 f1 f2
     ==>
     !h:num->num.
       (?k:num->num.
          (((!j:num.
               j < n1
               ==>
               p1 j = T
               ==>
               f1 j = f2 (h j)) /\
            logipedia_bigops_sub_hk h k n1 n2 p1 p2 f1 f2) /\
           logipedia_bigops_sub_hk k h n2 n1 p2 p1 f2 f1))
       ==>
       !k:num->num.
         (((!j:num.
              j < n1
              ==>
              p1 j = T
              ==>
              f1 j = f2 (h j)) /\
           logipedia_bigops_sub_hk h k n1 n2 p1 p2 f1 f2) /\
          logipedia_bigops_sub_hk k h n2 n1 p2 p1 f2 f1)
         ==>
         ((!j:num.
             j < n1
             ==>
             p1 j = T
             ==>
             f1 j = f2 (h j)) /\
          logipedia_bigops_sub_hk h k n1 n2 p1 p2 f1 f2)
         ==>
         (!j:num.
            j < n1
            ==>
            p1 j = T
            ==>
            f1 j = f2 (h j))
         ==>
         !i:num.
         !m:num.
           (!f:num->bool.
              0 <= n1
              ==>
              logipedia_bigops_sub_hk h k 0 m p1 f f1 f2
              ==>
              logipedia_bigops_sub_hk k h m 0 f p1 f2 f1
              ==>
              logipedia_bigops_bigop
                0 p1 1 (\x y:num. x * y) f1 =
              logipedia_bigops_bigop
                m f 1 (\x y:num. x * y) f2)
           ==>
           !p20:num->bool.
             0 <= n1
             ==>
             logipedia_bigops_sub_hk h k 0 (SUC m) p1 p20 f1 f2
             ==>
             logipedia_bigops_sub_hk k h (SUC m) 0 p20 p1 f2 f1
             ==>
             !x2571 x2572:num.
               x2571 =
               x2572 * (x2571 DIV x2572) + (x2571 MOD x2572)`;;
