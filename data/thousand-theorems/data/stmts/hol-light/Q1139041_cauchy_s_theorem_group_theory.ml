(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1139041,
  "Cauchy's theorem (group theory)": every prime divisor of the order of a
  finite group is the order of some element of the group. This file contains
  no proof.
*)

let Q1139041_CAUCHY_GROUP_THEOREM =
  `let dvd_rel =
     \d n:num. ?k:num. n = d * k in
   let is_prime =
     \p:num. 2 <= p /\ !d:num. dvd_rel d p ==> d = 1 \/ d = p in
   let is_group_on =
     \(s:A->bool) (op:A->A->A) (iinv:A->A) (id:A).
       id IN s /\
       (!x. x IN s ==> iinv x IN s) /\
       (!x y. x IN s /\ y IN s ==> op x y IN s) /\
       (!x y z.
          x IN s /\ y IN s /\ z IN s
          ==> op x (op y z) = op (op x y) z) /\
       (!x. x IN s ==> op id x = x /\ op x id = x) /\
       (!x. x IN s ==> op (iinv x) x = id /\ op x (iinv x) = id) in
   let is_power =
     \(op:A->A->A) (id:A) (x:A) (n:num) (y:A).
       ?f:num->A.
         f 0 = id /\
         (!k. k < n ==> f (k + 1) = op x (f k)) /\
         f n = y in
   !(s:A->bool) (op:A->A->A) (iinv:A->A) (id:A) (p:num).
     is_group_on s op iinv id /\
     FINITE s /\
     is_prime p /\
     dvd_rel p (CARD s)
     ==> ?x:A.
           x IN s /\
           !n:num. is_power op id x n id <=> dvd_rel p n`;;
