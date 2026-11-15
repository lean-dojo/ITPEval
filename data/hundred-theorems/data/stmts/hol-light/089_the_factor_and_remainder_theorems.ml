(* ========================================================================= *)
(* Properties of real polynomials (not canonically represented).             *)
(* ========================================================================= *)

needs "Library/analysis.ml";;

prioritize_real();;

parse_as_infix("++",(16,"right"));;
parse_as_infix("**",(20,"right"));;
parse_as_infix("##",(20,"right"));;
parse_as_infix("divides",(14,"right"));;
parse_as_infix("exp",(22,"right"));;

do_list override_interface
  ["++",`poly_add:real list->real list->real list`;
   "**",`poly_mul:real list->real list->real list`;
   "##",`poly_cmul:real->real list->real list`;
   "neg",`poly_neg:real list->real list`;
   "exp",`poly_exp:real list -> num -> real list`;
   "diff",`poly_diff:real list->real list`];;

overload_interface ("divides",`poly_divides:real list->real list->bool`);;

(* ------------------------------------------------------------------------- *)
(* Application of polynomial as a real function.                             *)
(* ------------------------------------------------------------------------- *)

let poly = new_recursive_definition list_RECURSION
  `(poly [] x = &0) /\
   (poly (CONS h t) x = h + x * poly t x)`;;

let POLY_CONST = `!c x. poly [c] x = c`;;

let POLY_X = `!c x. poly [&0; &1] x = x`;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations on polynomials.                                     *)
(* ------------------------------------------------------------------------- *)

let poly_add = new_recursive_definition list_RECURSION
  `([] ++ l2 = l2) /\
   ((CONS h t) ++ l2 =
        (if l2 = [] then CONS h t
                    else CONS (h + HD l2) (t ++ TL l2)))`;;

let poly_cmul = new_recursive_definition list_RECURSION
  `(c ## [] = []) /\
   (c ## (CONS h t) = CONS (c * h) (c ## t))`;;

let poly_neg = new_definition
  `neg = (##) (--(&1))`;;

let poly_mul = new_recursive_definition list_RECURSION
  `([] ** l2 = []) /\
   ((CONS h t) ** l2 =
       (if t = [] then h ## l2
                  else (h ## l2) ++ CONS (&0) (t ** l2)))`;;

let poly_exp = new_recursive_definition num_RECURSION
  `(p exp 0 = [&1]) /\
   (p exp (SUC n) = p ** p exp n)`;;

(* ------------------------------------------------------------------------- *)
(* Differentiation of polynomials (needs an auxiliary function).             *)
(* ------------------------------------------------------------------------- *)

let poly_diff_aux = new_recursive_definition list_RECURSION
  `(poly_diff_aux n [] = []) /\
   (poly_diff_aux n (CONS h t) = CONS (&n * h) (poly_diff_aux (SUC n) t))`;;

let poly_diff = new_definition
  `diff l = (if l = [] then [] else (poly_diff_aux 1 (TL l)))`;;

(* ------------------------------------------------------------------------- *)
(* Lengths.                                                                  *)
(* ------------------------------------------------------------------------- *)

let LENGTH_POLY_DIFF_AUX = `!l n. LENGTH(poly_diff_aux n l) = LENGTH l`;;

let LENGTH_POLY_DIFF = `!l. LENGTH(poly_diff l) = PRE(LENGTH l)`;;

(* ------------------------------------------------------------------------- *)
(* Useful clausifications.                                                   *)
(* ------------------------------------------------------------------------- *)

let POLY_ADD_CLAUSES = `([] ++ p2 = p2) /\
   (p1 ++ [] = p1) /\
   ((CONS h1 t1) ++ (CONS h2 t2) = CONS (h1 + h2) (t1 ++ t2))`;;

let POLY_CMUL_CLAUSES = `(c ## [] = []) /\
   (c ## (CONS h t) = CONS (c * h) (c ## t))`;;

let POLY_NEG_CLAUSES = `(neg [] = []) /\
   (neg (CONS h t) = CONS (--h) (neg t))`;;

let POLY_MUL_CLAUSES = `([] ** p2 = []) /\
   ([h1] ** p2 = h1 ## p2) /\
   ((CONS h1 (CONS k1 t1)) ** p2 = h1 ## p2 ++ CONS (&0) (CONS k1 t1 ** p2))`;;

let POLY_DIFF_CLAUSES = `(diff [] = []) /\
   (diff [c] = []) /\
   (diff (CONS h t) = poly_diff_aux 1 t)`;;

(* ------------------------------------------------------------------------- *)
(* Various natural consequences of syntactic definitions.                    *)
(* ------------------------------------------------------------------------- *)

let POLY_ADD = `!p1 p2 x. poly (p1 ++ p2) x = poly p1 x + poly p2 x`;;

let POLY_CMUL = `!p c x. poly (c ## p) x = c * poly p x`;;

let POLY_NEG = `!p x. poly (neg p) x = --(poly p x)`;;

let POLY_MUL = `!x p1 p2. poly (p1 ** p2) x = poly p1 x * poly p2 x`;;

let POLY_EXP = `!p n x. poly (p exp n) x = (poly p x) pow n`;;

(* ------------------------------------------------------------------------- *)
(* The derivative is a bit more complicated.                                 *)
(* ------------------------------------------------------------------------- *)

let POLY_DIFF_LEMMA = `!l n x. ((\x. (x pow (SUC n)) * poly l x) diffl
                   ((x pow n) * poly (poly_diff_aux (SUC n) l) x))(x)`;;

let POLY_DIFF = `!l x. ((\x. poly l x) diffl (poly (diff l) x))(x)`;;

(* ------------------------------------------------------------------------- *)
(* Trivial consequences.                                                     *)
(* ------------------------------------------------------------------------- *)

let POLY_DIFFERENTIABLE = `!l x. (\x. poly l x) differentiable x`;;

let POLY_CONT = `!l x. (\x. poly l x) contl x`;;

let POLY_IVT_POS = `!p a b. a < b /\ poly p a < &0 /\ poly p b > &0
           ==> ?x. a < x /\ x < b /\ (poly p x = &0)`;;

let POLY_IVT_NEG = `!p a b. a < b /\ poly p a > &0 /\ poly p b < &0
           ==> ?x. a < x /\ x < b /\ (poly p x = &0)`;;

let POLY_MVT = `!p a b. a < b ==>
           ?x. a < x /\ x < b /\
              (poly p b - poly p a = (b - a) * poly (diff p) x)`;;

let POLY_MVT_ADD = `!p a x. ?y. abs(y) <= abs(x) /\
               (poly p (a + x) = poly p a + x * poly (diff p) (a + y))`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let POLY_ADD_RZERO = `!p. poly (p ++ []) = poly p`;;

let POLY_MUL_ASSOC = `!p q r. poly (p ** (q ** r)) = poly ((p ** q) ** r)`;;

let POLY_EXP_ADD = `!d n p. poly(p exp (n + d)) = poly(p exp n ** p exp d)`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas for derivatives.                                                   *)
(* ------------------------------------------------------------------------- *)

let POLY_DIFF_AUX_ADD = `!p1 p2 n. poly (poly_diff_aux n (p1 ++ p2)) =
             poly (poly_diff_aux n p1 ++ poly_diff_aux n p2)`;;

let POLY_DIFF_AUX_CMUL = `!p c n. poly (poly_diff_aux n (c ## p)) =
           poly (c ## poly_diff_aux n p)`;;

let POLY_DIFF_AUX_NEG = `!p n.  poly (poly_diff_aux n (neg p)) =
          poly (neg (poly_diff_aux n p))`;;

let POLY_DIFF_AUX_MUL_LEMMA = `!p n. poly (poly_diff_aux (SUC n) p) = poly (poly_diff_aux n p ++ p)`;;

(* ------------------------------------------------------------------------- *)
(* Final results for derivatives.                                            *)
(* ------------------------------------------------------------------------- *)

let POLY_DIFF_ADD = `!p1 p2. poly (diff (p1 ++ p2)) =
           poly (diff p1  ++ diff p2)`;;

let POLY_DIFF_CMUL = `!p c. poly (diff (c ## p)) = poly (c ## diff p)`;;

let POLY_DIFF_NEG = `!p. poly (diff (neg p)) = poly (neg (diff p))`;;

let POLY_DIFF_MUL_LEMMA = `!t h. poly (diff (CONS h t)) =
         poly (CONS (&0) (diff t) ++ t)`;;

let POLY_DIFF_MUL = `!p1 p2. poly (diff (p1 ** p2)) =
           poly (p1 ** diff p2 ++ diff p1 ** p2)`;;

let POLY_DIFF_EXP = `!p n. poly (diff (p exp (SUC n))) =
         poly ((&(SUC n) ## (p exp n)) ** diff p)`;;

let POLY_DIFF_EXP_PRIME = `!n a. poly (diff ([--a; &1] exp (SUC n))) =
         poly (&(SUC n) ## ([--a; &1] exp n))`;;

(* ------------------------------------------------------------------------- *)
(* Key property that f(a) = 0 ==> (x - a) divides p(x). Very delicate!       *)
(* ------------------------------------------------------------------------- *)

let POLY_LINEAR_REM = `!t h. ?q r. CONS h t = [r] ++ [--a; &1] ** q`;;

let POLY_LINEAR_DIVIDES = `!a p. (poly p a = &0) <=> (p = []) \/ ?q. p = [--a; &1] ** q`;;

(* ------------------------------------------------------------------------- *)
(* Thanks to the finesse of the above, we can use length rather than degree. *)
(* ------------------------------------------------------------------------- *)

let POLY_LENGTH_MUL = `!q. LENGTH([--a; &1] ** q) = SUC(LENGTH q)`;;

(* ------------------------------------------------------------------------- *)
(* Thus a nontrivial polynomial of degree n has no more than n roots.        *)
(* ------------------------------------------------------------------------- *)

let POLY_ROOTS_INDEX_LEMMA = `!n. !p. ~(poly p = poly []) /\ (LENGTH p = n)
           ==> ?i. !x. (poly p (x) = &0) ==> ?m. m <= n /\ (x = i m)`;;

let POLY_ROOTS_INDEX_LENGTH = `!p. ~(poly p = poly [])
       ==> ?i. !x. (poly p(x) = &0) ==> ?n. n <= LENGTH p /\ (x = i n)`;;

let POLY_ROOTS_FINITE_LEMMA = `!p. ~(poly p = poly [])
       ==> ?N i. !x. (poly p(x) = &0) ==> ?n:num. n < N /\ (x = i n)`;;

let FINITE_LEMMA = `!i N P. (!x. P x ==> ?n:num. n < N /\ (x = i n))
           ==> ?a. !x. P x ==> x < a`;;

let POLY_ROOTS_FINITE = `!p. ~(poly p = poly []) <=>
       ?N i. !x. (poly p(x) = &0) ==> ?n:num. n < N /\ (x = i n)`;;

(* ------------------------------------------------------------------------- *)
(* Hence get entirety and cancellation for polynomials.                      *)
(* ------------------------------------------------------------------------- *)

let POLY_ENTIRE_LEMMA = `!p q. ~(poly p = poly []) /\ ~(poly q = poly [])
         ==> ~(poly (p ** q) = poly [])`;;

let POLY_ENTIRE = `!p q. (poly (p ** q) = poly []) <=>
         (poly p = poly []) \/ (poly q = poly [])`;;

let POLY_MUL_LCANCEL = `!p q r. (poly (p ** q) = poly (p ** r)) <=>
           (poly p = poly []) \/ (poly q = poly r)`;;

let POLY_EXP_EQ_0 = `!p n. (poly (p exp n) = poly []) <=> (poly p = poly []) /\ ~(n = 0)`;;

let POLY_PRIME_EQ_0 = `!a. ~(poly [a ; &1] = poly [])`;;

let POLY_EXP_PRIME_EQ_0 = `!a n. ~(poly ([a ; &1] exp n) = poly [])`;;

(* ------------------------------------------------------------------------- *)
(* Can also prove a more "constructive" notion of polynomial being trivial.  *)
(* ------------------------------------------------------------------------- *)

let POLY_ZERO_LEMMA = `!h t. (poly (CONS h t) = poly []) ==> (h = &0) /\ (poly t = poly [])`;;

let POLY_ZERO = `!p. (poly p = poly []) <=> ALL (\c. c = &0) p`;;

(* ------------------------------------------------------------------------- *)
(* Useful triviality.                                                        *)
(* ------------------------------------------------------------------------- *)

let POLY_DIFF_AUX_ISZERO = `!p n. ALL (\c. c = &0) (poly_diff_aux (SUC n) p) <=>
         ALL (\c. c = &0) p`;;

let POLY_DIFF_ISZERO = `!p. (poly (diff p) = poly []) ==> ?h. poly p = poly [h]`;;

let POLY_DIFF_ZERO = `!p. (poly p = poly []) ==> (poly (diff p) = poly [])`;;

let POLY_DIFF_WELLDEF = `!p q. (poly p = poly q) ==> (poly (diff p) = poly (diff q))`;;

(* ------------------------------------------------------------------------- *)
(* Basics of divisibility.                                                   *)
(* ------------------------------------------------------------------------- *)

let divides = new_definition
  `p1 divides p2 <=> ?q. poly p2 = poly (p1 ** q)`;;

let POLY_PRIMES = `!a p q. [a; &1] divides (p ** q) <=>
          [a; &1] divides p \/ [a; &1] divides q`;;

let POLY_DIVIDES_REFL = `!p. p divides p`;;

let POLY_DIVIDES_TRANS = `!p q r. p divides q /\ q divides r ==> p divides r`;;

let POLY_DIVIDES_EXP = `!p m n. m <= n ==> (p exp m) divides (p exp n)`;;

let POLY_EXP_DIVIDES = `!p q m n. (p exp n) divides q /\ m <= n ==> (p exp m) divides q`;;

let POLY_DIVIDES_ADD = `!p q r. p divides q /\ p divides r ==> p divides (q ++ r)`;;

let POLY_DIVIDES_SUB = `!p q r. p divides q /\ p divides (q ++ r) ==> p divides r`;;

let POLY_DIVIDES_SUB2 = `!p q r. p divides r /\ p divides (q ++ r) ==> p divides q`;;

let POLY_DIVIDES_ZERO = `!p q. (poly p = poly []) ==> q divides p`;;

(* ------------------------------------------------------------------------- *)
(* At last, we can consider the order of a root.                             *)
(* ------------------------------------------------------------------------- *)

let POLY_ORDER_EXISTS = `!a d. !p. (LENGTH p = d) /\ ~(poly p = poly [])
             ==> ?n. ([--a; &1] exp n) divides p /\
                     ~(([--a; &1] exp (SUC n)) divides p)`;;

let POLY_ORDER = `!p a. ~(poly p = poly [])
         ==> ?!n. ([--a; &1] exp n) divides p /\
                      ~(([--a; &1] exp (SUC n)) divides p)`;;

(* ------------------------------------------------------------------------- *)
(* Definition of order.                                                      *)
(* ------------------------------------------------------------------------- *)

let order = new_definition
  `order a p = @n. ([--a; &1] exp n) divides p /\
                   ~(([--a; &1] exp (SUC n)) divides p)`;;

let ORDER = `!p a n. ([--a; &1] exp n) divides p /\
           ~(([--a; &1] exp (SUC n)) divides p) <=>
           (n = order a p) /\
           ~(poly p = poly [])`;;

let ORDER_THM = `!p a. ~(poly p = poly [])
         ==> ([--a; &1] exp (order a p)) divides p /\
             ~(([--a; &1] exp (SUC(order a p))) divides p)`;;

let ORDER_UNIQUE = `!p a n. ~(poly p = poly []) /\
           ([--a; &1] exp n) divides p /\
           ~(([--a; &1] exp (SUC n)) divides p)
           ==> (n = order a p)`;;

let ORDER_POLY = `!p q a. (poly p = poly q) ==> (order a p = order a q)`;;

let ORDER_ROOT = `!p a. (poly p a = &0) <=> (poly p = poly []) \/ ~(order a p = 0)`;;

let ORDER_DIVIDES = `!p a n. ([--a; &1] exp n) divides p <=>
           (poly p = poly []) \/ n <= order a p`;;

let ORDER_DECOMP = `!p a. ~(poly p = poly [])
         ==> ?q. (poly p = poly (([--a; &1] exp (order a p)) ** q)) /\
                 ~([--a; &1] divides q)`;;

(* ------------------------------------------------------------------------- *)
(* Important composition properties of orders.                               *)
(* ------------------------------------------------------------------------- *)

let ORDER_MUL = `!a p q. ~(poly (p ** q) = poly []) ==>
           (order a (p ** q) = order a p + order a q)`;;

let ORDER_DIFF = `!p a. ~(poly (diff p) = poly []) /\
         ~(order a p = 0)
         ==> (order a p = SUC (order a (diff p)))`;;

(* ------------------------------------------------------------------------- *)
(* Now justify the standard squarefree decomposition, i.e. f / gcd(f,f').    *)
(* ------------------------------------------------------------------------- *)

let POLY_SQUAREFREE_DECOMP_ORDER = `!p q d e r s.
        ~(poly (diff p) = poly []) /\
        (poly p = poly (q ** d)) /\
        (poly (diff p) = poly (e ** d)) /\
        (poly d = poly (r ** p ++ s ** diff p))
        ==> !a. order a q = (if order a p = 0 then 0 else 1)`;;

(* ------------------------------------------------------------------------- *)
(* Define being "squarefree" --- NB with respect to real roots only.         *)
(* ------------------------------------------------------------------------- *)

let rsquarefree = new_definition
  `rsquarefree p <=> ~(poly p = poly []) /\
                     !a. (order a p = 0) \/ (order a p = 1)`;;

(* ------------------------------------------------------------------------- *)
(* Standard squarefree criterion and rephasing of squarefree decomposition.  *)
(* ------------------------------------------------------------------------- *)

let RSQUAREFREE_ROOTS = `!p. rsquarefree p <=> !a. ~((poly p a = &0) /\ (poly (diff p) a = &0))`;;

let RSQUAREFREE_DECOMP = `!p a. rsquarefree p /\ (poly p a = &0)
         ==> ?q. (poly p = poly ([--a; &1] ** q)) /\
                 ~(poly q a = &0)`;;

let POLY_SQUAREFREE_DECOMP = `!p q d e r s.
        ~(poly (diff p) = poly []) /\
        (poly p = poly (q ** d)) /\
        (poly (diff p) = poly (e ** d)) /\
        (poly d = poly (r ** p ++ s ** diff p))
        ==> rsquarefree q /\ (!a. (poly q a = &0) <=> (poly p a = &0))`;;

(* ------------------------------------------------------------------------- *)
(* Normalization of a polynomial.                                            *)
(* ------------------------------------------------------------------------- *)

let normalize = new_recursive_definition list_RECURSION
  `(normalize [] = []) /\
   (normalize (CONS h t) =
      if normalize t = [] then if h = &0 then [] else [h]
                          else CONS h (normalize t))`;;

let POLY_NORMALIZE = `!p. poly (normalize p) = poly p`;;

(* ------------------------------------------------------------------------- *)
(* The degree of a polynomial.                                               *)
(* ------------------------------------------------------------------------- *)

let degree = new_definition
  `degree p = PRE(LENGTH(normalize p))`;;

let DEGREE_ZERO = `!p. (poly p = poly []) ==> (degree p = 0)`;;

(* ------------------------------------------------------------------------- *)
(* Tidier versions of finiteness of roots.                                   *)
(* ------------------------------------------------------------------------- *)

let POLY_ROOTS_FINITE_SET = `!p. ~(poly p = poly []) ==> FINITE { x | poly p x = &0}`;;

(* ------------------------------------------------------------------------- *)
(* Crude bound for polynomial.                                               *)
(* ------------------------------------------------------------------------- *)

let POLY_MONO = `!x k p. abs(x) <= k ==> abs(poly p x) <= poly (MAP abs p) k`;;

(* ------------------------------------------------------------------------- *)
(* Conversions to perform operations if coefficients are rational constants. *)
(* ------------------------------------------------------------------------- *)

let POLY_DIFF_CONV =
  let aux_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 poly_diff_aux]
  and aux_conv1 = GEN_REWRITE_CONV I [CONJUNCT2 poly_diff_aux]
  and diff_conv0 = GEN_REWRITE_CONV I (butlast (CONJUNCTS POLY_DIFF_CLAUSES))
  and diff_conv1 = GEN_REWRITE_CONV I [last (CONJUNCTS POLY_DIFF_CLAUSES)] in
  let rec POLY_DIFF_AUX_CONV tm =
   (aux_conv0 ORELSEC
    (aux_conv1 THENC
     LAND_CONV REAL_RAT_MUL_CONV THENC
     RAND_CONV (LAND_CONV NUM_SUC_CONV THENC POLY_DIFF_AUX_CONV))) tm in
  diff_conv0 ORELSEC
  (diff_conv1 THENC POLY_DIFF_AUX_CONV);;

let POLY_CMUL_CONV =
  let cmul_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 poly_cmul]
  and cmul_conv1 = GEN_REWRITE_CONV I [CONJUNCT2 poly_cmul] in
  let rec POLY_CMUL_CONV tm =
   (cmul_conv0 ORELSEC
    (cmul_conv1 THENC
     LAND_CONV REAL_RAT_MUL_CONV THENC
     RAND_CONV POLY_CMUL_CONV)) tm in
  POLY_CMUL_CONV;;

let POLY_ADD_CONV =
  let add_conv0 = GEN_REWRITE_CONV I (butlast (CONJUNCTS POLY_ADD_CLAUSES))
  and add_conv1 = GEN_REWRITE_CONV I [last (CONJUNCTS POLY_ADD_CLAUSES)] in
  let rec POLY_ADD_CONV tm =
   (add_conv0 ORELSEC
    (add_conv1 THENC
     LAND_CONV REAL_RAT_ADD_CONV THENC
     RAND_CONV POLY_ADD_CONV)) tm in
  POLY_ADD_CONV;;

let POLY_MUL_CONV =
  let mul_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 POLY_MUL_CLAUSES]
  and mul_conv1 = GEN_REWRITE_CONV I [CONJUNCT1(CONJUNCT2 POLY_MUL_CLAUSES)]
  and mul_conv2 = GEN_REWRITE_CONV I [CONJUNCT2(CONJUNCT2 POLY_MUL_CLAUSES)] in
  let rec POLY_MUL_CONV tm =
   (mul_conv0 ORELSEC
    (mul_conv1 THENC POLY_CMUL_CONV) ORELSEC
    (mul_conv2 THENC
     LAND_CONV POLY_CMUL_CONV THENC
     RAND_CONV(RAND_CONV POLY_MUL_CONV) THENC
     POLY_ADD_CONV)) tm in
  POLY_MUL_CONV;;

let POLY_NORMALIZE_CONV =
  let pth = `normalize (CONS h t) =
      (\n. if n = [] then if h = &0 then [] else [h] else CONS h n)
      (normalize t)`;;

let NOT_POLY_MUL_NIL = `!p1 p2. ~(p1 = []) /\ ~(p2 = []) ==> ~((p1 ** p2) = [])`;;

let NOT_POLY_EXP_NIL = `!n p . ~(p = []) ==> ~((poly_exp p n) = [])`;;

let NOT_POLY_EXP_X_NIL = `!n. ~((poly_exp [&0;&1] n) = [])`;;

(* ------------------------------------------------------------------------- *)
(* Some general lemmas.                                                      *)
(* ------------------------------------------------------------------------- *)

let POLY_CMUL_LID = `!p. &1 ## p = p`;;

let POLY_MUL_LID = `!p. [&1] ** p = p`;;

let POLY_MUL_RID = `!p. p ** [&1] = p`;;

let POLY_ADD_SYM = `!x y . x ++ y = y ++ x`;;

let POLY_ADD_ASSOC = `!x y z . x ++ (y ++ z) = (x ++ y) ++ z`;;

(* ------------------------------------------------------------------------- *)
(* Heads and tails resulting from operations.                                *)
(* ------------------------------------------------------------------------- *)

let TL_POLY_MUL_X = `!p. TL ([&0;&1] ** p) = p`;;

let HD_POLY_MUL_X = `!p. HD ([&0;&1] ** p) = &0`;;

let TL_POLY_EXP_X_SUC = `!n . TL (poly_exp [&0;&1] (SUC n)) = poly_exp [&0;&1] n`;;

let HD_POLY_EXP_X_SUC = `!n . HD (poly_exp [&0;&1] (SUC n)) = &0`;;

let HD_POLY_ADD = `!p1 p2. ~(p1 = []) /\ ~(p2 = []) ==> HD (p1 ++ p2) = (HD p1) + (HD p2)`;;

let HD_POLY_CMUL = `!x p . ~(p = []) ==> HD (x ## p) = x * (HD p)`;;

let TL_POLY_CMUL = `!x p . ~(p = []) ==> TL (x ## p) = x ## (TL p)`;;

let HD_POLY_MUL = `!p1 p2 . ~(p1 = []) /\ ~(p2 = [])  ==> HD (p1 ** p2) = (HD p1) * (HD p2)`;;

let HD_POLY_EXP = `!n p . ~(p = []) ==> HD (poly_exp p n) = (HD p) pow n`;;

(* ------------------------------------------------------------------------- *)
(* Additional general lemmas.                                                *)
(* ------------------------------------------------------------------------- *)

let POLY_ADD_IDENT = `neutral (++) = []`;;

let POLY_ADD_NEUTRAL = `!x. neutral (++) ++ x = x`;;

let MONOIDAL_POLY_ADD = `monoidal poly_add`;;

let POLY_DIFF_AUX_ADD_LEMMA = `!t1 t2 n. poly_diff_aux n (t1 ++ t2) =
             (poly_diff_aux n t1) ++ (poly_diff_aux n t2)`;;

let POLYDIFF_ADD = `!p1 p2. (poly_diff (p1 ++ p2)) = (poly_diff p1  ++ poly_diff p2)`;;

let POLY_DIFF_AUX_POLY_CMUL = `!p c n. poly_diff_aux n (c ## p) = c ## (poly_diff_aux n p)`;;

let POLY_CMUL_POLY_DIFF = `!p c. poly_diff (c ## p) = c ## (poly_diff p)`;;

(* ------------------------------------------------------------------------- *)
(* Theorems about the lengths of lists from the polynomial operations.       *)
(* ------------------------------------------------------------------------- *)

let POLY_CMUL_LENGTH = `!c p. LENGTH (c ## p) =  LENGTH p`;;

let POLY_ADD_LENGTH = `!p q. LENGTH (p ++ q) =  MAX (LENGTH p) (LENGTH q)`;;

let POLY_MUL_LENGTH = `!p h t. LENGTH (p ** (CONS h t)) >= LENGTH p`;;

let POLY_EXP_X_REC = `!n. poly_exp [&0;&1] (SUC n) = CONS (&0) (poly_exp [&0;&1] n)`;;

let POLY_MUL_LENGTH2 = `!q p. ~(q = []) ==> LENGTH (p ** q) >= LENGTH p`;;

let POLY_EXP_X_LENGTH = `!n. LENGTH (poly_exp [&0;&1] n) = SUC n`;;

(* ------------------------------------------------------------------------- *)
(* Expansion of a polynomial as a power sum.                                 *)
(* ------------------------------------------------------------------------- *)

let POLY_SUM_EQUIV = `!p x.
     ~(p = []) ==>
     poly p x = sum (0..(PRE (LENGTH p))) (\i. (EL i p)*(x pow i))`;;

let ITERATE_RADD_POLYADD = `!n x f. iterate (+) (0..n) (\i.poly (f i) x) =
           poly (iterate (++) (0..n) f) x`;;

(* ------------------------------------------------------------------------- *)
(* Now we're finished with polynomials...                                    *)
(* ------------------------------------------------------------------------- *)

do_list reduce_interface
 ["divides",`poly_divides:real list->real list->bool`;
  "exp",`poly_exp:real list -> num -> real list`;
  "diff",`poly_diff:real list->real list`];;

unparse_as_infix "exp";;
