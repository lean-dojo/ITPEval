(*
  Statement-only formalization of Thousand Theorems corpus artifact Q4695203,
  "Four functions theorem": the Ahlswede-Daykin inequality for nonnegative
  functions on a distributive lattice and two finite sets. This file contains
  no proof.
*)

let Q4695203_FOUR_FUNCTIONS_THEOREM =
  `let is_distributive_lattice =
     \(le_rel:A->A->bool) (meet:A->A->A) (join:A->A->A).
       (!x. le_rel x x) /\
       (!x y z. le_rel x y /\ le_rel y z ==> le_rel x z) /\
       (!x y. le_rel x y /\ le_rel y x ==> x = y) /\
       (!x y z.
          (le_rel z (meet x y) <=> le_rel z x /\ le_rel z y)) /\
       (!x y z.
          (le_rel (join x y) z <=> le_rel x z /\ le_rel y z)) /\
       (!x y z.
          meet x (join y z) = join (meet x y) (meet x z)) /\
       (!x y z.
          join x (meet y z) = meet (join x y) (join x z)) in
   let is_ordered_comm_semiring =
     \(zero:B) (unitB:B) (add:B->B->B) (mul:B->B->B)
      (le_rel:B->B->bool).
       let lt_rel = \x y:B. le_rel x y /\ ~(x = y) in
       (!x y. add x y = add y x) /\
       (!x y z. add (add x y) z = add x (add y z)) /\
       (!x. add zero x = x /\ add x zero = x) /\
       (!x y. mul x y = mul y x) /\
       (!x y z. mul (mul x y) z = mul x (mul y z)) /\
       (!x. mul unitB x = x /\ mul x unitB = x) /\
       (!x. mul zero x = zero /\ mul x zero = zero) /\
       (!x y z.
          mul x (add y z) = add (mul x y) (mul x z) /\
          mul (add x y) z = add (mul x z) (mul y z)) /\
       (!x. le_rel x x) /\
       (!x y z. le_rel x y /\ le_rel y z ==> le_rel x z) /\
       (!x y. le_rel x y /\ le_rel y x ==> x = y) /\
       (!x y. le_rel x y \/ le_rel y x) /\
       (!a b c. le_rel a b ==> le_rel (add a c) (add b c)) /\
       (!a b c. le_rel a b ==> le_rel (add c a) (add c b)) /\
       (!a b c. le_rel (add a b) (add a c) ==> le_rel b c) /\
       (!a b c. le_rel (add b a) (add c a) ==> le_rel b c) /\
       le_rel zero unitB /\
       ~(zero = unitB) /\
       (!a b c.
          lt_rel zero a /\ lt_rel b c
          ==> lt_rel (mul a b) (mul a c)) /\
       (!a b c.
          lt_rel zero c /\ lt_rel a b
          ==> lt_rel (mul a c) (mul b c)) /\
       (!a b. le_rel a b ==> ?c. b = add a c) in
   let finite_sum =
     \(zero:B) (add:B->B->B) (s:A->bool) (f:A->B).
       ITSET (\x acc. add (f x) acc) s zero in
   let meet_family =
     \(meet:A->A->A) (s:A->bool) (t:A->bool).
       {x:A | ?a b. a IN s /\ b IN t /\ x = meet a b} in
   let join_family =
     \(join:A->A->A) (s:A->bool) (t:A->bool).
       {x:A | ?a b. a IN s /\ b IN t /\ x = join a b} in
   !(leA:A->A->bool) (meet:A->A->A) (join:A->A->A)
    (zero:B) (unitB:B) (add:B->B->B) (mul:B->B->B)
    (leB:B->B->bool) (f1:A->B) (f2:A->B) (f3:A->B) (f4:A->B)
    (s:A->bool) (t:A->bool).
      is_distributive_lattice leA meet join /\
      is_ordered_comm_semiring zero unitB add mul leB /\
      FINITE s /\ FINITE t /\
      (!x. leB zero (f1 x)) /\
      (!x. leB zero (f2 x)) /\
      (!x. leB zero (f3 x)) /\
      (!x. leB zero (f4 x)) /\
      (!a b.
         leB (mul (f1 a) (f2 b))
             (mul (f3 (meet a b)) (f4 (join a b))))
      ==>
      leB
        (mul (finite_sum zero add s f1)
             (finite_sum zero add t f2))
        (mul (finite_sum zero add (meet_family meet s t) f3)
             (finite_sum zero add (join_family join s t) f4))`;;
