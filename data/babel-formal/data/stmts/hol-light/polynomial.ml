let mynat_INDUCT,mynat_RECURSION = define_type
 "mynat = Nat_O | Nat_S mynat";;

let mynat_add = new_recursive_definition mynat_RECURSION
 `(mynat_add Nat_O m = m) /\
  (mynat_add (Nat_S n) m = Nat_S (mynat_add n m))`;;

let mynat_add_O_left =
  `!m. mynat_add Nat_O m = m`;;

let mynat_add_S_left =
  `!n m. mynat_add (Nat_S n) m = Nat_S (mynat_add n m)`;;

let mynat_le_RULES,mynat_le_INDUCT,mynat_le_CASES = new_inductive_definition
 `(!n. mynat_le n n) /\
  (!n m. mynat_le n m ==> mynat_le n (Nat_S m))`;;

let mynat_zero_le =
  `!n. mynat_le Nat_O n`;;

let mynat_add_zero_r =
  `!n. mynat_add n Nat_O = n`;;

let mynat_succ_le_succ =
  `!n m. mynat_le n m ==> mynat_le (Nat_S n) (Nat_S m)`;;

let mynat_add_S_r =
  `!m n. mynat_add m (Nat_S n) = Nat_S (mynat_add m n)`;;

let mynat_add_comm =
  `!n m. mynat_add n m = mynat_add m n`;;

let mynat_le_add_left =
  `!n m. mynat_le n (mynat_add m n)`;;

let mylist_INDUCT,mylist_RECURSION = define_type
 "mylist = NilL | ConsL A mylist";;

let InL_RULES,InL_INDUCT,InL_CASES = new_inductive_definition
 `(!x xs. InL x (ConsL x xs)) /\
  (!x y xs. InL x xs ==> InL x (ConsL y xs))`;;

let NoDupL_RULES,NoDupL_INDUCT,NoDupL_CASES = new_inductive_definition
 `NoDupL NilL /\
  (!x xs. ~(InL x xs) /\ NoDupL xs ==> NoDupL (ConsL x xs))`;;

let InL_cons_intro =
  `!x y (xs:A mylist). InL x xs ==> InL x (ConsL y xs)`;;

let NoDupL_cons_tail =
  `!x (xs:A mylist). NoDupL (ConsL x xs) ==> NoDupL xs`;;

let NoDupL_cons_notin =
  `!x (xs:A mylist). NoDupL (ConsL x xs) ==> ~(InL x xs)`;;

let lengthL = new_recursive_definition mylist_RECURSION
 `(lengthL NilL = Nat_O) /\
  (lengthL (ConsL x xs) = Nat_S (lengthL xs))`;;

let X = new_definition
 `X (monomial:mynat->R->P) (oneR:R) = monomial (Nat_S Nat_O) oneR`;;

let C = new_definition
 `C (monomial:mynat->R->P) (c:R) = monomial Nat_O c`;;

let x_minus_def = new_definition
 `X_minus (monomial:mynat->R->P) (addP:P->P->P) (oppR:R->R)
          (oneR:R) (a:R) =
    addP (X monomial oneR) (C monomial (oppR a))`;;

let is_root = new_definition
 `is_root (eval:P->R->R) (zeroR:R) (a:R) (p:P) <=> eval p a = zeroR`;;

let poly_of_roots = new_recursive_definition mylist_RECURSION
 `(poly_of_roots (monomial:mynat->R->P) (addP:P->P->P) (oppR:R->R)
                 (oneR:R) (mulP:P->P->P) (oneP:P) NilL = oneP) /\
  (poly_of_roots monomial addP oppR oneR mulP oneP (ConsL a xs) =
     mulP (X_minus monomial addP oppR oneR a)
          (poly_of_roots monomial addP oppR oneR mulP oneP xs))`;;

let is_ring = new_definition
 `is_ring (zr:A) (un:A) (add:A->A->A) (mul:A->A->A) (opp:A->A) <=>
    ~(un = zr) /\
    (!x y. add x y = add y x) /\
    (!x y z. add (add x y) z = add x (add y z)) /\
    (!x. add x zr = x) /\
    (!x. add x (opp x) = zr) /\
    (!x y. mul x y = mul y x) /\
    (!x y z. mul (mul x y) z = mul x (mul y z)) /\
    (!x. mul x un = x) /\
    (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
    (!x. mul x zr = zr) /\
    (!x y. mul x y = zr ==> x = zr \/ y = zr)`;;

let is_poly_context = new_definition
 `is_poly_context
      (zeroR:R) (oneR:R) (addR:R->R->R) (mulR:R->R->R) (oppR:R->R)
      (zeroP:P) (oneP:P) (addP:P->P->P) (mulP:P->P->P) (oppP:P->P)
      (degree:P->mynat) (monomial:mynat->R->P) (eval:P->R->R) <=>
    is_ring zeroR oneR addR mulR oppR /\
    is_ring zeroP oneP addP mulP oppP /\
    C monomial zeroR = zeroP /\
    C monomial oneR = oneP /\
    degree zeroP = Nat_O /\
    (!p q x. eval (addP p q) x = addR (eval p x) (eval q x)) /\
    (!p q x. eval (mulP p q) x = mulR (eval p x) (eval q x)) /\
    (!c x. eval (C monomial c) x = c) /\
    (!x. eval (X monomial oneR) x = x) /\
    (!c. ~(c = zeroR) ==> degree (C monomial c) = Nat_O) /\
    (!p. degree p = Nat_O <=> ?c. p = C monomial c) /\
    (!a. degree (X_minus monomial addP oppR oneR a) = Nat_S Nat_O) /\
    (!p q. ~(p = zeroP) /\ ~(q = zeroP)
           ==> degree (mulP p q) = mynat_add (degree p) (degree q)) /\
    (!p a. ?q r. p = addP (mulP q (X_minus monomial addP oppR oneR a)) r /\
                  degree r = Nat_O)`;;

let ring_add_comm =
  `!zr un add mul opp (x:A) y.
     is_ring zr un add mul opp ==> add x y = add y x`;;

let ring_add_assoc =
  `!zr un add mul opp (x:A) y z.
     is_ring zr un add mul opp ==> add (add x y) z = add x (add y z)`;;

let ring_add_zero =
  `!zr un add mul opp (x:A).
     is_ring zr un add mul opp ==> add x zr = x`;;

let ring_add_opp =
  `!zr un add mul opp (x:A).
     is_ring zr un add mul opp ==> add x (opp x) = zr`;;

let poly_context_poly_ring =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> is_ring zeroP oneP addP mulP oppP`;;

let poly_context_oneP_nonzero =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> ~(oneP = zeroP)`;;

let poly_context_oneP_degree =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> degree oneP = Nat_O`;;

let poly_context_zeroP_degree =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> degree zeroP = Nat_O`;;

let poly_context_x_minus_degree =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> degree (X_minus monomial addP oppR oneR a) = Nat_S Nat_O`;;

let poly_context_mul_degree =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) q.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> ~(p = zeroP) /\ ~(q = zeroP)
     ==> degree (mulP p q) = mynat_add (degree p) (degree q)`;;

let ring_mul_comm =
  `!zr un add mul opp (x:A) y.
     is_ring zr un add mul opp ==> mul x y = mul y x`;;

let ring_mul_assoc =
  `!zr un add mul opp (x:A) y z.
     is_ring zr un add mul opp ==> mul (mul x y) z = mul x (mul y z)`;;

let ring_mul_reassoc_comm =
  `!zr un add mul opp (x:A) y z.
     is_ring zr un add mul opp ==> mul (mul x y) z = mul x (mul z y)`;;

let ring_mul_one =
  `!zr un add mul opp (x:A).
     is_ring zr un add mul opp ==> mul x un = x`;;

let ring_mul_zero =
  `!zr un add mul opp (x:A).
     is_ring zr un add mul opp ==> mul x zr = zr`;;

let ring_no_zero_div =
  `!zr un add mul opp (x:A) y.
     is_ring zr un add mul opp ==> mul x y = zr ==> x = zr \/ y = zr`;;

let ring_mul_zero_left =
  `!zr un add mul opp (x:A).
     is_ring zr un add mul opp ==> mul zr x = zr`;;

let sub_eq_zero_l =
  `!zeroR oneR addR mulR oppR (a:R) b.
     is_ring zeroR oneR addR mulR oppR
     ==> addR a (oppR b) = zeroR ==> a = b`;;

let eval_x_minus_self =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> eval (X_minus monomial addP oppR oneR a) a = zeroR`;;

let eval_x_minus =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (a:R) b.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> eval (X_minus monomial addP oppR oneR a) b = addR b (oppR a)`;;

let poly_context_division =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> ?q r. p = addP (mulP q (X_minus monomial addP oppR oneR a)) r /\
               degree r = Nat_O`;;

let poly_context_C_zero =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> C monomial zeroR = zeroP`;;

let poly_context_eval_C =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (c:R) x.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> eval (C monomial c) x = c`;;

let poly_context_degree_zero =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> (degree p = Nat_O <=> ?c. p = C monomial c)`;;

let poly_context_base_ring =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> is_ring zeroR oneR addR mulR oppR`;;

let poly_context_eval_add =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) q x.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> eval (addP p q) x = addR (eval p x) (eval q x)`;;

let poly_context_eval_mul =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) q x.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> eval (mulP p q) x = mulR (eval p x) (eval q x)`;;

let ring_add_zero_left =
  `!zr un add mul opp (x:A).
     is_ring zr un add mul opp ==> add zr x = x`;;

let ring_add_zero_left_eq =
  `!zr un add mul opp (x:A).
     is_ring zr un add mul opp ==> add zr x = zr ==> x = zr`;;

let poly_context_add_zero =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (x:P).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> addP x zeroP = x`;;

let ring_add_mul_zero_cancel =
  `!zr un add mul opp (x:A) y.
     is_ring zr un add mul opp ==> add (mul x zr) y = zr ==> y = zr`;;

let constant_root_zero_lemma =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> degree p = Nat_O ==> is_root eval zeroR a p ==> p = zeroP`;;

let root_factor_remainder_root =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) q r (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
	     ==> p = addP (mulP q (X_minus monomial addP oppR oneR a)) r
	     ==> is_root eval zeroR a p
	     ==> is_root eval zeroR a r`;;

let root_factor_remainder_zero =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) q r (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> p = addP (mulP q (X_minus monomial addP oppR oneR a)) r
     ==> degree r = Nat_O
     ==> is_root eval zeroR a p
     ==> r = zeroP`;;

let root_factor =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> is_root eval zeroR a p
     ==> ?q. p = mulP q (X_minus monomial addP oppR oneR a)`;;

let root_transfer =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) q (a:R) b.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> p = mulP q (X_minus monomial addP oppR oneR a)
     ==> ~(b = a)
     ==> is_root eval zeroR b p
     ==> is_root eval zeroR b q`;;

let x_minus_nonzero =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> ~(X_minus monomial addP oppR oneR a = zeroP)`;;

let constant_root_zero = constant_root_zero_lemma;;

let root_of_product =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) q (a:R).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> is_root eval zeroR a (mulP p q)
     ==> is_root eval zeroR a p \/ is_root eval zeroR a q`;;

let root_scale_constant =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) (c:R) a.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> ~(c = zeroR)
     ==> (is_root eval zeroR a p <=>
          is_root eval zeroR a (mulP (C monomial c) p))`;;

let poly_of_roots_nonzero =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (xs:R mylist).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> ~(poly_of_roots monomial addP oppR oneR mulP oneP xs = zeroP)`;;

let poly_context_x_roots_mul_degree =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (a:R) (xs:R mylist).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
         degree monomial eval
     ==> degree (mulP (X_minus monomial addP oppR oneR a)
                   (poly_of_roots monomial addP oppR oneR mulP oneP xs)) =
         mynat_add (degree (X_minus monomial addP oppR oneR a))
                   (degree (poly_of_roots monomial addP oppR oneR mulP oneP xs))`;;

let deg_poly_of_roots =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (xs:R mylist).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> degree (poly_of_roots monomial addP oppR oneR mulP oneP xs) =
         lengthL xs`;;

let root_factor_list =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) (xs:R mylist).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> NoDupL xs
     ==> (!a. InL a xs ==> is_root eval zeroR a p)
     ==> ?q. p = mulP q (poly_of_roots monomial addP oppR oneR mulP oneP xs)`;;

let degree_factorisation =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) (xs:R mylist) q.
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> p = mulP q (poly_of_roots monomial addP oppR oneR mulP oneP xs)
     ==> ~(q = zeroP)
     ==> degree p = mynat_add (degree q) (lengthL xs)`;;

let roots_le_degree =
  `!zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
     degree monomial eval (p:P) (xs:R mylist).
     is_poly_context zeroR oneR addR mulR oppR zeroP oneP addP mulP oppP
                     degree monomial eval
     ==> NoDupL xs
     ==> (!a. InL a xs ==> is_root eval zeroR a p)
     ==> ~(p = zeroP)
     ==> mynat_le (lengthL xs) (degree p)`;;
