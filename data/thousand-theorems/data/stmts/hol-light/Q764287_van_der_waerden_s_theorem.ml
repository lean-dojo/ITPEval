(*
  Statement-only formalization of Thousand Theorems corpus artifact Q764287
  (thousand-theorems__hol-light__Q764287), "Van der Waerden's theorem": every
  finite subset of a finitely colored additive commutative monoid has a
  monochromatic homothetic copy with positive natural dilation. This file
  contains no proof.
*)

let Q764287_VAN_DER_WAERDENS_THEOREM =
  `let is_add_comm_monoid =
     \(zero:A) (add:A->A->A).
       (!x:A. add zero x = x /\ add x zero = x) /\
       (!x y:A. add x y = add y x) /\
       (!x y z:A. add (add x y) z = add x (add y z)) in
   let natural_multiple =
     \(zero:A) (add:A->A->A) (n:num) (x:A).
       ITLIST add (REPLICATE n x) zero in
   !zero:A. !add:A->A->A. !S:A->bool. !C:A->B.
     is_add_comm_monoid zero add /\
     FINITE S /\
     FINITE (UNIV:B->bool)
     ==> ?a:num.
           0 < a /\
           ?b:A. ?c:B.
             !s:A.
               s IN S
               ==> C (add (natural_multiple zero add a s) b) = c`;;
