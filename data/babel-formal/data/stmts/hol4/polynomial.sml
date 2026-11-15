(*
  Statement-only formalization of the Babel-formal artifact polynomial:
  factorization by linear root factors and the bound on distinct roots of a
  nonzero polynomial over an abstract integral domain. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib arithmeticTheory listTheory;

val _ = new_theory "hello";

val babel_mynat_add_def = new_definition (
  "babel_mynat_add_def",
  ``babel_mynat_add (n : num) m = n + m``);

val babel_mynat_le_def = new_definition (
  "babel_mynat_le_def",
  ``babel_mynat_le (n : num) m <=> n <= m``);

val babel_InL_def = new_definition (
  "babel_InL_def",
  ``babel_InL (x : 'a) (xs : 'a list) <=> MEM x xs``);

val babel_NoDupL_def = new_definition (
  "babel_NoDupL_def",
  ``babel_NoDupL (xs : 'a list) <=> ALL_DISTINCT xs``);

val babel_lengthL_def = new_definition (
  "babel_lengthL_def",
  ``babel_lengthL (xs : 'a list) = LENGTH xs``);

val mynat_add_O_left =
  ``!(m : num). babel_mynat_add 0 m = m``;

val mynat_add_S_left =
  ``!(n : num) m.
      babel_mynat_add (SUC n) m = SUC (babel_mynat_add n m)``;

val mynat_zero_le =
  ``!(n : num). babel_mynat_le 0 n``;

val mynat_add_zero_r =
  ``!(n : num). babel_mynat_add n 0 = n``;

val mynat_succ_le_succ =
  ``!(n : num) m.
      babel_mynat_le n m ==> babel_mynat_le (SUC n) (SUC m)``;

val mynat_add_S_r =
  ``!(m : num) n.
      babel_mynat_add m (SUC n) = SUC (babel_mynat_add m n)``;

val mynat_add_comm =
  ``!(n : num) m. babel_mynat_add n m = babel_mynat_add m n``;

val babel_integral_domain_def = new_definition (
  "babel_integral_domain_def",
  ``babel_integral_domain
      (zeroA : 'a) (oneA : 'a)
      (addA : 'a -> 'a -> 'a) (mulA : 'a -> 'a -> 'a)
      (oppA : 'a -> 'a) <=>
      ~(oneA = zeroA) /\
      (!x y. addA x y = addA y x) /\
      (!x y z. addA (addA x y) z = addA x (addA y z)) /\
      (!x. addA x zeroA = x) /\
      (!x. addA x (oppA x) = zeroA) /\
      (!x y. mulA x y = mulA y x) /\
      (!x y z. mulA (mulA x y) z = mulA x (mulA y z)) /\
      (!x. mulA x oneA = x) /\
      (!x y z.
         mulA x (addA y z) = addA (mulA x y) (mulA x z)) /\
      (!x. mulA x zeroA = zeroA) /\
      (!x y. mulA x y = zeroA ==> x = zeroA \/ y = zeroA)``);

val babel_X_def = new_definition (
  "babel_X_def",
  ``babel_X (monomial : num -> 'r -> 'p) (oneR : 'r) =
      monomial (SUC 0) oneR``);

val babel_C_def = new_definition (
  "babel_C_def",
  ``babel_C (monomial : num -> 'r -> 'p) (c : 'r) =
      monomial 0 c``);

val babel_X_minus_def = new_definition (
  "babel_X_minus_def",
  ``babel_X_minus
      (monomial : num -> 'r -> 'p) (addP : 'p -> 'p -> 'p)
      (oppR : 'r -> 'r) (oneR : 'r) (a : 'r) =
      addP (babel_X monomial oneR) (babel_C monomial (oppR a))``);

val babel_is_root_def = new_definition (
  "babel_is_root_def",
  ``babel_is_root (eval : 'p -> 'r -> 'r) (zeroR : 'r)
      (a : 'r) (p : 'p) <=>
      eval p a = zeroR``);

val babel_poly_of_roots_def = new_definition (
  "babel_poly_of_roots_def",
  ``babel_poly_of_roots
      (monomial : num -> 'r -> 'p) (addP : 'p -> 'p -> 'p)
      (oppR : 'r -> 'r) (oneR : 'r)
      (mulP : 'p -> 'p -> 'p) (oneP : 'p) (xs : 'r list) =
      FOLDR
        (\a acc. mulP (babel_X_minus monomial addP oppR oneR a) acc)
        oneP xs``);

val babel_poly_context_def = new_definition (
  "babel_poly_context_def",
  ``babel_poly_context
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroP : 'p) (oneP : 'p)
      (addP : 'p -> 'p -> 'p) (mulP : 'p -> 'p -> 'p)
      (oppP : 'p -> 'p)
      (degree : 'p -> num) (monomial : num -> 'r -> 'p)
      (eval : 'p -> 'r -> 'r) <=>
      babel_integral_domain zeroR oneR addR mulR oppR /\
      babel_integral_domain zeroP oneP addP mulP oppP /\
      babel_C monomial zeroR = zeroP /\
      babel_C monomial oneR = oneP /\
      degree zeroP = 0 /\
      (!p q x. eval (addP p q) x = addR (eval p x) (eval q x)) /\
      (!p q x. eval (mulP p q) x = mulR (eval p x) (eval q x)) /\
      (!c x. eval (babel_C monomial c) x = c) /\
      (!x. eval (babel_X monomial oneR) x = x) /\
      (!c. ~(c = zeroR) ==> degree (babel_C monomial c) = 0) /\
      (!p. degree p = 0 <=> ?c. p = babel_C monomial c) /\
      (!a.
         degree (babel_X_minus monomial addP oppR oneR a) = SUC 0) /\
      (!p q.
         ~(p = zeroP) /\ ~(q = zeroP) ==>
         degree (mulP p q) =
           babel_mynat_add (degree p) (degree q)) /\
      (!p a.
         ?q r.
           p =
             addP
               (mulP q (babel_X_minus monomial addP oppR oneR a))
               r /\
           degree r = 0)``);

val sub_eq_zero_l =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (a : 'r) b.
      babel_integral_domain zeroR oneR addR mulR oppR ==>
      addR a (oppR b) = zeroR ==>
      a = b``;

val root_factor =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroP : 'p) (oneP : 'p)
      (addP : 'p -> 'p -> 'p) (mulP : 'p -> 'p -> 'p)
      (oppP : 'p -> 'p)
      (degree : 'p -> num) (monomial : num -> 'r -> 'p)
      (eval : 'p -> 'r -> 'r) (p : 'p) (a : 'r).
      babel_poly_context zeroR oneR addR mulR oppR
        zeroP oneP addP mulP oppP degree monomial eval ==>
      babel_is_root eval zeroR a p ==>
      ?q. p = mulP q (babel_X_minus monomial addP oppR oneR a)``;

val root_transfer =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroP : 'p) (oneP : 'p)
      (addP : 'p -> 'p -> 'p) (mulP : 'p -> 'p -> 'p)
      (oppP : 'p -> 'p)
      (degree : 'p -> num) (monomial : num -> 'r -> 'p)
      (eval : 'p -> 'r -> 'r) (p : 'p) q (a : 'r) b.
      babel_poly_context zeroR oneR addR mulR oppR
        zeroP oneP addP mulP oppP degree monomial eval ==>
      p = mulP q (babel_X_minus monomial addP oppR oneR a) ==>
      ~(b = a) ==>
      babel_is_root eval zeroR b p ==>
      babel_is_root eval zeroR b q``;

val roots_le_degree =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroP : 'p) (oneP : 'p)
      (addP : 'p -> 'p -> 'p) (mulP : 'p -> 'p -> 'p)
      (oppP : 'p -> 'p)
      (degree : 'p -> num) (monomial : num -> 'r -> 'p)
      (eval : 'p -> 'r -> 'r) (p : 'p) (xs : 'r list).
      babel_poly_context zeroR oneR addR mulR oppR
        zeroP oneP addP mulP oppP degree monomial eval ==>
      babel_NoDupL xs ==>
      (!a. babel_InL a xs ==> babel_is_root eval zeroR a p) ==>
      ~(p = zeroP) ==>
      babel_mynat_le (babel_lengthL xs) (degree p)``;

val X_minus_nonzero =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroP : 'p) (oneP : 'p)
      (addP : 'p -> 'p -> 'p) (mulP : 'p -> 'p -> 'p)
      (oppP : 'p -> 'p)
      (degree : 'p -> num) (monomial : num -> 'r -> 'p)
      (eval : 'p -> 'r -> 'r) (a : 'r).
      babel_poly_context zeroR oneR addR mulR oppR
        zeroP oneP addP mulP oppP degree monomial eval ==>
      ~(babel_X_minus monomial addP oppR oneR a = zeroP)``;

val constant_root_zero =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroP : 'p) (oneP : 'p)
      (addP : 'p -> 'p -> 'p) (mulP : 'p -> 'p -> 'p)
      (oppP : 'p -> 'p)
      (degree : 'p -> num) (monomial : num -> 'r -> 'p)
      (eval : 'p -> 'r -> 'r) (p : 'p) (a : 'r).
      babel_poly_context zeroR oneR addR mulR oppR
        zeroP oneP addP mulP oppP degree monomial eval ==>
      degree p = 0 ==>
      babel_is_root eval zeroR a p ==>
      p = zeroP``;

val root_of_product =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroP : 'p) (oneP : 'p)
      (addP : 'p -> 'p -> 'p) (mulP : 'p -> 'p -> 'p)
      (oppP : 'p -> 'p)
      (degree : 'p -> num) (monomial : num -> 'r -> 'p)
      (eval : 'p -> 'r -> 'r) (p : 'p) q (a : 'r).
      babel_poly_context zeroR oneR addR mulR oppR
        zeroP oneP addP mulP oppP degree monomial eval ==>
      babel_is_root eval zeroR a (mulP p q) ==>
      babel_is_root eval zeroR a p \/
      babel_is_root eval zeroR a q``;

val root_scale_constant =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroP : 'p) (oneP : 'p)
      (addP : 'p -> 'p -> 'p) (mulP : 'p -> 'p -> 'p)
      (oppP : 'p -> 'p)
      (degree : 'p -> num) (monomial : num -> 'r -> 'p)
      (eval : 'p -> 'r -> 'r) (p : 'p) (c : 'r) a.
      babel_poly_context zeroR oneR addR mulR oppR
        zeroP oneP addP mulP oppP degree monomial eval ==>
      ~(c = zeroR) ==>
      (babel_is_root eval zeroR a p <=>
       babel_is_root eval zeroR a (mulP (babel_C monomial c) p))``;

val poly_of_roots_nonzero =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroP : 'p) (oneP : 'p)
      (addP : 'p -> 'p -> 'p) (mulP : 'p -> 'p -> 'p)
      (oppP : 'p -> 'p)
      (degree : 'p -> num) (monomial : num -> 'r -> 'p)
      (eval : 'p -> 'r -> 'r) (xs : 'r list).
      babel_poly_context zeroR oneR addR mulR oppR
        zeroP oneP addP mulP oppP degree monomial eval ==>
      ~(babel_poly_of_roots monomial addP oppR oneR mulP oneP xs =
        zeroP)``;

val deg_poly_of_roots =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroP : 'p) (oneP : 'p)
      (addP : 'p -> 'p -> 'p) (mulP : 'p -> 'p -> 'p)
      (oppP : 'p -> 'p)
      (degree : 'p -> num) (monomial : num -> 'r -> 'p)
      (eval : 'p -> 'r -> 'r) (xs : 'r list).
      babel_poly_context zeroR oneR addR mulR oppR
        zeroP oneP addP mulP oppP degree monomial eval ==>
      degree
        (babel_poly_of_roots monomial addP oppR oneR mulP oneP xs) =
      babel_lengthL xs``;

val root_factor_list =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroP : 'p) (oneP : 'p)
      (addP : 'p -> 'p -> 'p) (mulP : 'p -> 'p -> 'p)
      (oppP : 'p -> 'p)
      (degree : 'p -> num) (monomial : num -> 'r -> 'p)
      (eval : 'p -> 'r -> 'r) (p : 'p) (xs : 'r list).
      babel_poly_context zeroR oneR addR mulR oppR
        zeroP oneP addP mulP oppP degree monomial eval ==>
      babel_NoDupL xs ==>
      (!a. babel_InL a xs ==> babel_is_root eval zeroR a p) ==>
      ?q.
        p =
          mulP q
            (babel_poly_of_roots
              monomial addP oppR oneR mulP oneP xs)``;

val degree_factorisation =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r)
      (zeroP : 'p) (oneP : 'p)
      (addP : 'p -> 'p -> 'p) (mulP : 'p -> 'p -> 'p)
      (oppP : 'p -> 'p)
      (degree : 'p -> num) (monomial : num -> 'r -> 'p)
      (eval : 'p -> 'r -> 'r)
      (p : 'p) (xs : 'r list) (q : 'p).
      babel_poly_context zeroR oneR addR mulR oppR
        zeroP oneP addP mulP oppP degree monomial eval ==>
      p =
        mulP q
          (babel_poly_of_roots monomial addP oppR oneR mulP oneP xs) ==>
      ~(q = zeroP) ==>
      degree p =
        babel_mynat_add (degree q) (babel_lengthL xs)``;

val _ = export_theory();
