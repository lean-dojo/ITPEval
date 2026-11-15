(* ========================================================================= *)
(* Basic theory of divisibility, gcd, coprimality and primality (over N).    *)
(* ========================================================================= *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elementary theory of divisibility                                         *)
(* ------------------------------------------------------------------------- *)

let DIVIDES_0 = `!x. x divides 0`;;

let DIVIDES_ZERO = `!x. 0 divides x <=> x = 0`;;

let DIVIDES_1 = `!x. 1 divides x`;;

let DIVIDES_REFL = `!x. x divides x`;;

let DIVIDES_TRANS = `!a b c. a divides b /\ b divides c ==> a divides c`;;

let DIVIDES_ADD = `!d a b. d divides a /\ d divides b ==> d divides (a + b)`;;

let DIVIDES_SUB_EQ = `!d a b. d divides (a - b) <=> a < b \/ (a == b) (mod d)`;;

let DIVIDES_SUB = `!d a b. d divides a /\ d divides b ==> d divides (a - b)`;;

let DIVIDES_SUB_1 = `!d n. d divides n - 1 <=> n = 0 \/ (n == 1) (mod d)`;;

let DIVIDES_LMUL = `!d a x. d divides a ==> d divides (x * a)`;;

let DIVIDES_RMUL = `!d a x. d divides a ==> d divides (a * x)`;;

let DIVIDES_ADD_REVR = `!d a b. d divides a /\ d divides (a + b) ==> d divides b`;;

let DIVIDES_ADD_REVL = `!d a b. d divides b /\ d divides (a + b) ==> d divides a`;;

let DIVIDES_MUL_L = `!a b c. a divides b ==> (c * a) divides (c * b)`;;

let DIVIDES_MUL_R = `!a b c. a divides b ==> (a * c) divides (b * c)`;;

let DIVIDES_LMUL2 = `!d a x. (x * d) divides a ==> d divides a`;;

let DIVIDES_RMUL2 = `!d a x. (d * x) divides a ==> d divides a`;;

let DIVIDES_CMUL2 = `!a b c. (c * a) divides (c * b) /\ ~(c = 0) ==> a divides b`;;

let DIVIDES_LMUL2_EQ = `!a b c. ~(c = 0) ==> ((c * a) divides (c * b) <=> a divides b)`;;

let DIVIDES_RMUL2_EQ = `!a b c. ~(c = 0) ==> ((a * c) divides (b * c) <=> a divides b)`;;

let DIVIDES_EQ_ZERO = `!p n. n < p ==> (p divides n <=> n = 0)`;;

let DIVIDES_CASES = `!m n. n divides m ==> m = 0 \/ m = n \/ 2 * n <= m`;;

let DIVIDES_DIV_NOT = `!n x q r. x = q * n + r /\ 0 < r /\ r < n ==> ~(n divides x)`;;

let DIVIDES_MUL2 = `!a b c d. a divides b /\ c divides d ==> (a * c) divides (b * d)`;;

let DIVIDES_EXP = `!x y n. x divides y ==> (x EXP n) divides (y EXP n)`;;

let DIVIDES_EXP2 = `!n x y. ~(n = 0) /\ (x EXP n) divides y ==> x divides y`;;

let DIVIDES_EXP_LE_IMP = `!p m n. m <= n ==> (p EXP m) divides (p EXP n)`;;

let DIVIDES_EXP_LE = `!p m n. 2 <= p ==> ((p EXP m) divides (p EXP n) <=> m <= n)`;;

let DIVIDES_TRIVIAL_UPPERBOUND = `!p n. ~(n = 0) /\ 2 <= p ==> ~((p EXP n) divides n)`;;

let DIVIDES_FACT = `!n p. 1 <= p /\ p <= n ==> p divides (FACT n)`;;

let DIVIDES_2 = `!n. 2 divides n <=> EVEN(n)`;;

let DIVIDES_REXP_SUC = `!x y n. x divides y ==> x divides (y EXP (SUC n))`;;

let DIVIDES_REXP = `!x y n. x divides y /\ ~(n = 0) ==> x divides (y EXP n)`;;

let FINITE_DIVISORS = `!n. ~(n = 0) ==> FINITE {d | d divides n}`;;

let FINITE_SPECIAL_DIVISORS = `!n. ~(n = 0) ==> FINITE {d | P d /\ d divides n}`;;

let DIVISORS_EQ = `!m n. m = n <=> !d. d divides m <=> d divides n`;;

let MULTIPLES_EQ = `!m n. m = n <=> !d. m divides d <=> n divides d`;;

let DIVIDES_NSUM = `!n f s. FINITE s /\ (!i. i IN s ==> n divides (f i))
           ==> n divides nsum s f`;;

(* ------------------------------------------------------------------------- *)
(* Greatest common divisor.                                                  *)
(* ------------------------------------------------------------------------- *)

let DIVIDES_GCD = `!a b d. d divides gcd(a,b) <=> d divides a /\ d divides b`;;

let GCD_0 = `(!a. gcd(0,a) = a) /\ (!a. gcd(a,0) = a)`;;

let GCD_ZERO = `!a b. gcd(a,b) = 0 <=> a = 0 /\ b = 0`;;

let GCD_REFL = `!a. gcd(a,a) = a`;;

let GCD_1 = `(!a. gcd(1,a) = 1) /\ (!a. gcd(a,1) = 1)`;;

let GCD_MULTIPLE = `!a b. gcd(b,a * b) = b`;;

let GCD_ADD = `(!a b. gcd(a + b,b) = gcd(a,b)) /\
   (!a b. gcd(b + a,b) = gcd(a,b)) /\
   (!a b. gcd(a,a + b) = gcd(a,b)) /\
   (!a b. gcd(a,b + a) = gcd(a,b))`;;

let GCD_SUB = `(!a b. b <= a ==> gcd(a - b,b) = gcd(a,b)) /\
   (!a b. a <= b ==> gcd(a,b - a) = gcd(a,b))`;;

let DIVIDES_GCD_LEFT = `!m n:num. m divides n <=> gcd(m,n) = m`;;

let DIVIDES_GCD_RIGHT = `!m n:num. n divides m <=> gcd(m,n) = n`;;

let GCD_COPRIME_LMUL = `!a b c. coprime(a,b) ==> gcd(a * b,c) = gcd(a,c) * gcd(b,c)`;;

let GCD_COPRIME_RMUL = `!a b c. coprime(a,b) ==> gcd(c,a * b) = gcd(c,a) * gcd(c,b)`;;

let DIVIDES_LMUL_GCD = `(!d a b. d divides gcd(d,a) * b <=> d divides a * b) /\
   (!d a b. d divides gcd(a,d) * b <=> d divides a * b)`;;

let DIVIDES_RMUL_GCD = `(!d a b. d divides a * gcd(d,b) <=> d divides a * b) /\
   (!d a b. d divides a * gcd(b,d) <=> d divides a * b)`;;

let GCD_MUL_COPRIME = `(!a b c. coprime(a,b) ==> gcd(a,b * c) = gcd(a,c)) /\
   (!a b c. coprime(a,c) ==> gcd(a,b * c) = gcd(a,b)) /\
   (!a b c. coprime(b,c) ==> gcd(a,b * c) = gcd(a,b) * gcd(a,c)) /\
   (!a b c. coprime(a,c) ==> gcd(a * b,c) = gcd(b,c)) /\
   (!a b c. coprime(b,c) ==> gcd(a * b,c) = gcd(a,c)) /\
   (!a b c. coprime(a,b) ==> gcd(a * b,c) = gcd(a,c) * gcd(b,c))`;;

let GCD_SYM = `!a b. gcd(a,b) = gcd(b,a)`;;

let GCD_ASSOC = `!a b c. gcd(a,gcd(b,c)) = gcd(gcd(a,b),c)`;;

let GCD_LMUL = `!a b c. gcd(c * a, c * b) = c * gcd(a,b)`;;

let GCD_RMUL = `!a b c. gcd(a * c, b * c) = c * gcd(a,b)`;;

let GCD_BEZOUT_SUM = `!a b d x y. a * x + b * y = d ==> gcd(a,b) divides d`;;

let GCD_COPRIME_DIVIDES_LMUL = `!a b c:num. coprime(a,b) /\ a divides c ==> gcd(a * b,c) = a * gcd(b,c)`;;

let GCD_COPRIME_DIVIDES_RMUL = `!a b c:num. coprime(b,c) /\ b divides a ==> gcd(a,b * c) = b * gcd(a,c)`;;

let GCD_UNIQUE = `!d a b. (d divides a /\ d divides b) /\
           (!e. e divides a /\ e divides b ==> e divides d) <=>
           d = gcd(a,b)`;;

let GCD_EQ = `(!d. d divides x /\ d divides y <=> d divides u /\ d divides v)
   ==> gcd(x,y) = gcd(u,v)`;;

let BEZOUT_GCD_STRONG = `!a b. ~(a = 0) ==> ?x y. a * x = b * y + gcd(a,b)`;;

let BEZOUT_ADD_STRONG = `!a b. ~(a = 0)
         ==> ?d x y. d divides a /\ d divides b /\ a * x = b * y + d`;;

let BEZOUT_GCD = `!a b. ?x y. a * x - b * y = gcd(a,b) \/ b * x - a * y = gcd(a,b)`;;

let BEZOUT_ADD = `!a b. ?d x y. (d divides a /\ d divides b) /\
                 (a * x = b * y + d \/ b * x = a * y + d)`;;

let BEZOUT = `!a b. ?d x y. (d divides a /\ d divides b) /\
                 (a * x - b * y = d \/ b * x - a * y = d)`;;

let GCD_BEZOUT = `!a b d. (?x y. a * x - b * y = d \/ b * x - a * y = d) <=>
           gcd(a,b) divides d`;;

let GCD_LE = `(!m n. gcd(m,n) <= m <=> (m = 0 ==> n = 0)) /\
   (!m n. gcd(m,n) <= n <=> (n = 0 ==> m = 0))`;;

let GCD_LE_MIN_EQ = `!m n. gcd(m,n) <= MIN m n <=> (m = 0 <=> n = 0)`;;

let GCD_LE_MIN = `!m n. (m = 0 <=> n = 0) ==> gcd(m,n) <= MIN m n`;;

let GCD_LE_MAX = `!m n. gcd(m,n) <= MAX m n`;;

(* ------------------------------------------------------------------------- *)
(* Coprimality                                                               *)
(* ------------------------------------------------------------------------- *)

let COPRIME = `!a b. coprime(a,b) <=> !d. d divides a /\ d divides b <=> d = 1`;;

let COPRIME_GCD = `!a b. coprime(a,b) <=> gcd(a,b) = 1`;;

let GCD_ONE = `!a b. coprime(a,b) ==> gcd(a,b) = 1`;;

let COPRIME_SYM = `!a b. coprime(a,b) <=> coprime(b,a)`;;

let COPRIME_BEZOUT = `!a b. coprime(a,b) <=> ?x y. a * x - b * y = 1 \/ b * x - a * y = 1`;;

let COPRIME_DIVPROD = `!d a b. d divides (a * b) /\ coprime(d,a) ==> d divides b`;;

let COPRIME_1 = `(!a. coprime(a,1)) /\ (!a. coprime(1,a))`;;

let GCD_COPRIME = `!a b a' b'. ~(gcd(a,b) = 0) /\ a = a' * gcd(a,b) /\ b = b' * gcd(a,b)
               ==> coprime(a',b')`;;

let GCD_COPRIME_EXISTS = `!a b. ?a' b'. a = a' * gcd(a,b) /\ b = b' * gcd(a,b) /\ coprime(a',b')`;;

let COPRIME_DIVPROD_IFF = `!d a. ~(d = 0)
         ==> ((!b. d divides a * b ==> d divides b) <=> coprime(d,a))`;;

let CONG_MULT_LCANCEL_IFF = `!a n. ~(n = 0)
         ==> ((!x y. (a * x == a * y) (mod n) ==> (x == y) (mod n)) <=>
              coprime(a,n))`;;

let CONG_MULT_RCANCEL_IFF = `!a n. ~(n = 0)
         ==> ((!x y. (x * a == y * a) (mod n) ==> (x == y) (mod n)) <=>
              coprime(a,n))`;;

let COPRIME_0 = `(!d. coprime(d,0) <=> d = 1) /\
   (!d. coprime(0,d) <=> d = 1)`;;

let COPRIME_MUL = `!d a b. coprime(d,a) /\ coprime(d,b) ==> coprime(d,a * b)`;;

let COPRIME_LMUL2 = `!d a b. coprime(d,a * b) ==> coprime(d,b)`;;

let COPRIME_RMUL2 = `!d a b.  coprime(d,a * b) ==> coprime(d,a)`;;

let COPRIME_LMUL = `!d a b. coprime(a * b,d) <=> coprime(a,d) /\ coprime(b,d)`;;

let COPRIME_RMUL = `!d a b. coprime(d,a * b) <=> coprime(d,a) /\ coprime(d,b)`;;

let COPRIME_EXP = `!n a d. coprime(d,a) ==> coprime(d,a EXP n)`;;

let COPRIME_EXP_IMP = `!n a b. coprime(a,b) ==> coprime(a EXP n,b EXP n)`;;

let COPRIME_REXP = `!m n k. coprime(m,n EXP k) <=> coprime(m,n) \/ k = 0`;;

let COPRIME_LEXP = `!m n k. coprime(m EXP k,n) <=> coprime(m,n) \/ k = 0`;;

let COPRIME_EXP2 = `!m n k. coprime(m EXP k,n EXP k) <=> coprime(m,n) \/ k = 0`;;

let COPRIME_EXP2_SUC = `!n a b. coprime(a EXP (SUC n),b EXP (SUC n)) <=> coprime(a,b)`;;

let COPRIME_NPRODUCT_EQ = `(!(f:A->num) a s.
        FINITE s
        ==> (coprime(a,nproduct s f) <=> !i. i IN s ==> coprime(a,f i))) /\
   (!(f:A->num) b s.
        FINITE s
        ==> (coprime(nproduct s f,b) <=> !i. i IN s ==> coprime(f i,b)))`;;

let COPRIME_NPRODUCT = `!s n. FINITE s /\ (!x. x IN s ==> coprime(n,a x))
         ==> coprime(n,nproduct s a)`;;

let COPRIME_DIVISORS = `!a b d e. d divides a /\ e divides b /\ coprime(a,b) ==> coprime(d,e)`;;

let COPRIME_REFL = `!n. coprime(n,n) <=> n = 1`;;

let COPRIME_PLUS1 = `!n. coprime(n + 1,n)`;;

let COPRIME_MINUS1 = `!n. ~(n = 0) ==> coprime(n - 1,n)`;;

let GCD_EXP = `!n a b. gcd(a EXP n,b EXP n) = gcd(a,b) EXP n`;;

let DIVIDES_EXP2_REV = `!n a b. (a EXP n) divides (b EXP n) /\ ~(n = 0) ==> a divides b`;;

let DIVIDES_EXP2_EQ = `!n a b. ~(n = 0) ==> ((a EXP n) divides (b EXP n) <=> a divides b)`;;

let DIVIDES_MUL = `!m n r. m divides r /\ n divides r /\ coprime(m,n) ==> (m * n) divides r`;;

let DIVISION_DECOMP = `!a b c.
        a divides (b * c)
        ==> ?b' c'. a = b' * c' /\ b' divides b /\ c' divides c`;;

(* ------------------------------------------------------------------------- *)
(* Primes.                                                                   *)
(* ------------------------------------------------------------------------- *)

let PRIME_0 = `~prime(0)`;;

let PRIME_1 = `~prime(1)`;;

let PRIME_ALT = `!p. prime p <=>
       ~(p = 0) /\ ~(p = 1) /\ !n. 1 < n /\ n < p ==> ~(n divides p)`;;

let PRIME_2 = `prime(2)`;;

let PRIME_COPRIME_STRONG = `!n p. prime(p) ==> p divides n \/ coprime(p,n)`;;

let PRIME_COPRIME = `!n p. prime(p) ==> n = 1 \/ p divides n \/ coprime(p,n)`;;

let PRIME_COPRIME_EQ = `!p n. prime p ==> (coprime(p,n) <=> ~(p divides n))`;;

let COPRIME_PRIME = `!p a b. coprime(a,b) ==> ~(prime(p) /\ p divides a /\ p divides b)`;;

let PRIME_DIVPROD = `!p a b. prime(p) /\ p divides (a * b) ==> p divides a \/ p divides b`;;

let PRIME_DIVPROD_EQ = `!p a b. prime(p) ==> (p divides (a * b) <=> p divides a \/ p divides b)`;;

let PRIME_INT_DIVPROD_EQ = `!p a b:int.
        prime p ==> (&p divides a * b <=> &p divides a \/ &p divides b)`;;

let PRIME_GE_2 = `!p. prime(p) ==> 2 <= p`;;

let PRIME_FACTOR = `!n. ~(n = 1) ==> ?p. prime(p) /\ p divides n`;;

let PRIME = `!p. prime p <=>
       ~(p = 0) /\ ~(p = 1) /\ !m. 0 < m /\ m < p ==> coprime(p,m)`;;

let PRIME_PRIME_FACTOR = `!n. prime n <=> ~(n = 1) /\ !p. prime p /\ p divides n ==> p = n`;;

let PRIME_FACTOR_LT = `!n m p. prime(p) /\ ~(n = 0) /\ n = p * m ==> m < n`;;

let COPRIME_PRIME_EQ = `!a b. coprime(a,b) <=> !p. ~(prime(p) /\ p divides a /\ p divides b)`;;

let GCD_PRIME_CASES = `(!p n. prime p ==> gcd(p,n) = if p divides n then p else 1) /\
   (!p n. prime p ==> gcd(n,p) = if p divides n then p else 1)`;;

let GCD_2_CASES = `(!n. gcd(2,n) = if EVEN n then 2 else 1) /\
   (!n. gcd(n,2) = if EVEN n then 2 else 1)`;;

let COPRIME_PRIMEPOW = `!p k m. prime p /\ ~(k = 0) ==> (coprime(m,p EXP k) <=> ~(p divides m))`;;

let COPRIME_BEZOUT_STRONG = `!a b. coprime(a,b) /\ ~(b = 1) ==> ?x y. a * x = b * y + 1`;;

let COPRIME_BEZOUT_ALT = `!a b. coprime(a,b) /\ ~(a = 0) ==> ?x y. a * x = b * y + 1`;;

let BEZOUT_PRIME = `!a p. prime p /\ ~(p divides a) ==> ?x y. a * x = p * y + 1`;;

let PRIME_DIVEXP = `!n p x. prime(p) /\ p divides (x EXP n) ==> p divides x`;;

let PRIME_DIVEXP_N = `!n p x. prime(p) /\ p divides (x EXP n) ==> (p EXP n) divides (x EXP n)`;;

let PRIME_DIVEXP_EQ = `!n p x. prime p ==> (p divides x EXP n <=> p divides x /\ ~(n = 0))`;;

let COPRIME_SOS = `!x y. coprime(x,y) ==> coprime(x * y,(x EXP 2) + (y EXP 2))`;;

let PRIME_IMP_NZ = `!p. prime(p) ==> ~(p = 0)`;;

let DISTINCT_PRIME_COPRIME = `!p q. prime p /\ prime q /\ ~(p = q) ==> coprime(p,q)`;;

let PRIME_COPRIME_LT = `!x p. prime p /\ 0 < x /\ x < p ==> coprime(x,p)`;;

let DIVIDES_PRIME_PRIME = `!p q. prime p /\ prime q  ==> (p divides q <=> p = q)`;;

let COPRIME_PRIME_PRIME = `!p q. prime p /\ prime q ==> (coprime(p,q) <=> ~(p = q))`;;

let DIVIDES_PRIME_EXP_LE = `!p q m n. prime p /\ prime q
             ==> ((p EXP m) divides (q EXP n) <=> m = 0 \/ p = q /\ m <= n)`;;

let EQ_PRIME_EXP = `!p q m n. prime p /\ prime q
             ==> (p EXP m = q EXP n <=> m = 0 /\ n = 0 \/ p = q /\ m = n)`;;

let PRIME_ODD = `!p. prime p ==> p = 2 \/ ODD p`;;

let ODD_PRIME = `!p. prime p ==> (ODD p <=> 3 <= p)`;;

let DIVIDES_FACT_PRIME = `!p. prime p ==> !n. p divides (FACT n) <=> p <= n`;;

let EQ_PRIMEPOW = `!p m n. prime p ==> (p EXP m = p EXP n <=> m = n)`;;

let COPRIME_2 = `(!n. coprime(2,n) <=> ODD n) /\ (!n. coprime(n,2) <=> ODD n)`;;

let DIVIDES_EXP_PLUS1 = `!n k. ODD k ==> (n + 1) divides (n EXP k + 1)`;;

let DIVIDES_EXP_MINUS1 = `!k n. (n - 1) divides (n EXP k - 1)`;;

let PRIME_IRREDUCIBLE = `!p. prime p <=>
       p > 1 /\ !a b. p divides (a * b) ==> p divides a \/ p divides b`;;

let COPRIME_EXP_DIVPROD = `!d n a b.
      (d EXP n) divides (a * b) /\ coprime(d,a) ==> (d EXP n) divides b`;;

let PRIME_COPRIME_CASES = `!p a b. prime p /\ coprime(a,b) ==> coprime(p,a) \/ coprime(p,b)`;;

let PRIME_DIVPROD_POW_GEN = `!n p a b.
        prime p /\ ~(p divides gcd(a,b)) /\ p EXP n divides a * b
        ==> p EXP n divides a \/ p EXP n divides b`;;

let PRIME_DIVPROD_POW_GEN_EQ = `!n p a b.
        prime p /\ ~(p divides gcd(a,b))
        ==> (p EXP n divides a * b <=>
             p EXP n divides a \/ p EXP n divides b)`;;

let PRIME_DIVPROD_POW = `!n p a b. prime(p) /\ coprime(a,b) /\ (p EXP n) divides (a * b)
             ==> (p EXP n) divides a \/ (p EXP n) divides b`;;

let PRIME_DIVPROD_POW_EQ = `!n p a b.
        prime p /\ coprime(a,b)
        ==> (p EXP n divides a * b <=>
             p EXP n divides a \/ p EXP n divides b)`;;

let PRIME_FACTOR_INDUCT = `!P. P 0 /\ P 1 /\
       (!p n. prime p /\ ~(n = 0) /\ P n ==> P(p * n))
       ==> !n. P n`;;

let COMPLETE_FACTOR_INDUCT = `!P. P 0 /\ P 1 /\
       (!p. prime p ==> P p) /\
       (!m n. P m /\ P n ==> P(m * n))
       ==> !n. P n`;;

let PRIME_FACTOR_PARTITION = `!Q n. ~(n = 0)
         ==> ?n1 n2. n1 * n2 = n /\
                     (!p. prime p /\ p divides n1 ==> Q p) /\
                     (!p. prime p /\ p divides n2 ==> ~Q p)`;;

let COPRIME_PAIR_DECOMP = `!n1 n2 m.
        coprime(n1,n2) /\ ~(m = 0)
        ==> ?m1 m2. coprime(m1,n1) /\ coprime(m2,n2) /\
                    coprime(m1,m2) /\ m1 * m2 = m`;;

let EXP_MULT_EXISTS = `!m n p k. ~(m = 0) /\ m EXP k * n = p EXP k ==> ?q. n = q EXP k`;;

let COPRIME_POW = `!n a b c. coprime(a,b) /\ a * b = c EXP n
             ==> ?r s. a = r EXP n /\ b = s EXP n`;;

let PRIME_EXP = `!p n. prime(p EXP n) <=> prime(p) /\ (n = 1)`;;

let PRIME_POWER_MULT = `!k x y p. prime p /\ (x * y = p EXP k)
           ==> ?i j. (x = p EXP i) /\ (y = p EXP j)`;;

let PRIME_POWER_EXP = `!n x p k. prime p /\ ~(n = 0) /\ (x EXP n = p EXP k) ==> ?i. x = p EXP i`;;

let DIVIDES_PRIMEPOW = `!p. prime p ==> !d. d divides (p EXP k) <=> ?i. i <= k /\ d = p EXP i`;;

let PRIMEPOW_DIVIDES_PROD = `!p k m n.
        prime p /\ (p EXP k) divides (m * n)
        ==> ?i j. (p EXP i) divides m /\ (p EXP j) divides n /\ k = i + j`;;

let EUCLID_BOUND = `!n. ?p. prime(p) /\ n < p /\ p <= SUC(FACT n)`;;

let EUCLID = `!n. ?p. prime(p) /\ p > n`;;

let PRIMES_INFINITE = `INFINITE {p | prime p}`;;

let FACTORIZATION_INDEX = `!n p. ~(n = 0) /\ 2 <= p
         ==> ?k. (p EXP k) divides n /\
                 !l. k < l ==> ~((p EXP l) divides n)`;;

let PRIMEPOW_FACTOR = `!n. 2 <= n
       ==> ?p k m. prime p /\ 1 <= k /\ coprime(p,m) /\ n = p EXP k * m`;;

let PRIMEPOW_DIVISORS_DIVIDES = `!m n. m divides n <=>
         !p k. prime p /\ p EXP k divides m ==> p EXP k divides n`;;

let PRIMEPOW_DIVISORS_EQ = `!m n. m = n <=>
         !p k. prime p ==> (p EXP k divides m <=> p EXP k divides n)`;;

(* ------------------------------------------------------------------------- *)
(* A binary form of the Chinese Remainder Theorem.                           *)
(* ------------------------------------------------------------------------- *)

let CHINESE_REMAINDER = `!a b u v. coprime(a,b) /\ ~(a = 0) /\ ~(b = 0)
             ==> ?x q1 q2. x = u + q1 * a /\ x = v + q2 * b`;;

(* ------------------------------------------------------------------------- *)
(* Index of a (usually prime) divisor of a number.                           *)
(* ------------------------------------------------------------------------- *)

let FINITE_EXP_LE = `!P p n. 2 <= p ==> FINITE {j | P j /\ p EXP j <= n}`;;

let FINITE_INDICES = `!P p n. 2 <= p /\ ~(n = 0) ==> FINITE {j | P j /\ p EXP j divides n}`;;

let index_def = new_definition
 `index p n = if p <= 1 \/ n = 0 then 0
              else CARD {j | 1 <= j /\ p EXP j divides n}`;;

let INDEX_0 = `!p. index p 0 = 0`;;

let PRIMEPOW_DIVIDES_INDEX = `!n p k. p EXP k divides n <=> n = 0 \/ p = 1 \/ k <= index p n`;;

let LE_INDEX = `!n p k. k <= index p n <=> (n = 0 \/ p = 1 ==> k = 0) /\ p EXP k divides n`;;

let EXP_INDEX_DIVIDES = `!p n. p EXP (index p n) divides n`;;

let INDEX_LT = `!n p k. (~(n = 0) \/ ~(k = 0)) /\ n < p EXP k ==> index p n < k`;;

let INDEX_1 = `!p. index p 1 = 0`;;

let INDEX_MUL = `!m n. prime p /\ ~(m = 0) /\ ~(n = 0)
         ==> index p (m * n) = index p m + index p n`;;

let INDEX_EXP = `!p n k. prime p ==> index p (n EXP k) = k * index p n`;;

let INDEX_FACT = `!p n. prime p ==> index p (FACT n) = nsum(1..n) (\m. index p m)`;;

let INDEX_FACT_ALT = `!p n. prime p
         ==> index p (FACT n) =
             nsum {j | 1 <= j /\ p EXP j <= n} (\j. n DIV (p EXP j))`;;

let INDEX_FACT_UNBOUNDED = `!p n. prime p
         ==> index p (FACT n) = nsum {j | 1 <= j} (\j. n DIV (p EXP j))`;;

let PRIMEPOW_DIVIDES_FACT = `!p n k. prime p
           ==> (p EXP k divides FACT n <=>
                k <= nsum {j | 1 <= j /\ p EXP j <= n} (\j. n DIV (p EXP j)))`;;

let INDEX_REFL = `!n. index n n = if n <= 1 then 0 else 1`;;

let INDEX_EQ_0 = `!p n. index p n = 0 <=> n = 0 \/ p = 1 \/ ~(p divides n)`;;

let INDEX_ZERO = `!p n. ~(p divides n) ==> index p n = 0`;;

let INDEX_POW = `!p n k. index (p EXP k) n = index p n DIV k`;;

let INDEX_PRIME = `!p a. prime p ==> index a p = if p = a then 1 else 0`;;

let INDEX_TRIVIAL_BOUND = `!n p. index p n <= n`;;

let INDEX_DECOMPOSITION = `!n p. ?m. p EXP (index p n) * m = n /\ (n = 0 \/ p = 1 \/ ~(p divides m))`;;

let INDEX_DECOMPOSITION_PRIME = `!n p. prime p ==> ?m. p EXP (index p n) * m = n /\ (n = 0 \/ coprime(p,m))`;;

let INDEX_DECOMPOSITION_LE = `!p e1 m1 e2 m2.
    p EXP e1 * m1 = p EXP e2 * m2 /\ ~(p = 0) /\ ~(p divides m2) ==> e1 <= e2`;;

let INDEX_DECOMPOSITION_UNIQUE = `!p e1 m1 e2 m2.
        p EXP e1 * m1 = p EXP e2 * m2 /\
        ~(p = 0) /\ ~(p divides m1) /\ ~(p divides m2)
        ==> e1 = e2`;;

let INDEX_UNIQUE = `!p m n e.
        p EXP e * m = n /\ (p = 0 ==> e = 0) /\ ~(p divides m)
        ==> index p n = e`;;

let INDEX_UNIQUE_EQ = `!n p k. index p n = k <=>
           if p = 1 \/ n = 0 then k = 0
           else !j. p EXP j divides n <=> j <= k`;;

let INDEX_UNIQUE_ALT = `!n p k. index p n = k <=>
           if p = 1 \/ n = 0 then k = 0
           else p EXP k divides n /\ ~(p EXP (k + 1) divides n)`;;

let INDEX_ADD_MIN = `!p m n. MIN (index p m) (index p n) <= index p (m + n)`;;

let INDEX_SUB_MIN = `!p m n. n < m ==> MIN (index p m) (index p n) <= index p (m - n)`;;

let INDEX_ADD = `!p n m.
        ~(n = 0) /\ (~(m = 0) ==> index p n < index p m)
        ==> index p (m + n) = index p n`;;

let INDEX_MULT_BASE = `(!p n. index p (p * n) = if p <= 1 \/ n = 0 then 0 else index p n + 1) /\
   (!p n. index p (n * p) = if p <= 1 \/ n = 0 then 0 else index p n + 1)`;;

let INDEX_MULT_EXP = `(!p n k. index p (p EXP k * n) =
            if p <= 1 \/ n = 0 then 0 else k + index p n) /\
   (!p n k. index p (n * p EXP k) =
            if n = 0 \/ p <= 1 then 0 else index p n + k)`;;

let INDEX_MULT_ADD = `(!p m n k.
        ~(n = 0) /\ index p n < k ==> index p (p EXP k * m + n) = index p n) /\
   (!p m n k.
        ~(n = 0) /\ index p n < k ==> index p (m * p EXP k + n) = index p n) /\
   (!p m n k.
        ~(n = 0) /\ index p n < k ==> index p (n + m * p EXP k) = index p n) /\
   (!p m n k.
        ~(n = 0) /\ index p n < k ==> index p (n + p EXP k * m) = index p n)`;;

let INDEX_NSUM_LE = `!(f:A->num) p n k.
         FINITE k /\ ~(k = {}) /\ (!a. a IN k ==> n <= index p (f a))
         ==> n <= index p (nsum k f)`;;

let DIVIDES_INDEX = `!m n. m divides n <=>
         n = 0 \/ ~(m = 0) /\ !p. prime p ==> index p m <= index p n`;;

let EQ_INDEX = `!m n. m = n <=> (m = 0 <=> n = 0) /\ !p. prime p ==> index p m = index p n`;;

let COPRIME_INDEX = `!m n. coprime(m,n) <=>
         (m = 0 ==> n = 1) /\ (n = 0 ==> m = 1) /\
         !p. prime p ==> index p m = 0 \/ index p n = 0`;;

let INDEX_GCD = `!m n p.
        prime p
        ==> index p (gcd(m,n)) =
            if m = 0 then index p n
            else if n = 0 then index p m
            else MIN (index p m) (index p n)`;;

let FORALL_PRIME_INDEX = `(!p. prime p ==> !P. ((!x. P(index p x)) <=> !k. P k)) /\
   (!p. prime p ==> !P. ((!x. ~(x = 0) ==> P(index p x)) <=> !k. P k))`;;

let INDEX_FACT_PRIME_MULT = `!p n. prime p ==> index p (FACT(p * n)) = n + index p (FACT n)`;;

let PRIME_FACTORIZATION_INDEX = `!k. FINITE {p | prime p /\ ~(k p = 0)}
       ==> ?n. ~(n = 0) /\ !p. prime p ==> index p n = k p`;;

let PRIME_POWER_EXISTS = `!n q. prime q
         ==> ((?i. n = q EXP i) <=>
              (!p. prime p /\ p divides n ==> p = q))`;;

let PRIME_POWER_EXISTS_ALT = `!n p.
         prime p
         ==> ((?i. n = p EXP i) <=>
              (!d. d divides n ==> d = 1 \/ p divides d))`;;

let PRIME_FACTORIZATION_ALT = `!n. ~(n = 0) ==> nproduct {p | prime p} (\p. p EXP index p n) = n`;;

let PRIME_FACTORIZATION = `!n. ~(n = 0)
       ==> nproduct {p | prime p /\ p divides n} (\p. p EXP index p n) = n`;;

(* ------------------------------------------------------------------------- *)
(* Least common multiples.                                                   *)
(* ------------------------------------------------------------------------- *)

let lcm = `lcm(m,n) = if m * n = 0 then 0 else (m * n) DIV gcd(m,n)`;;

let LCM_DIVIDES = `!m n d. lcm(m,n) divides d <=> m divides d /\ n divides d`;;

let LCM = `!m n. m divides lcm(m,n) /\
         n divides lcm(m,n) /\
         (!d. m divides d /\ n divides d ==> lcm(m,n) divides d)`;;

let LCM_DIVIDES_MUL = `!m n. lcm(m,n) divides m * n`;;

let DIVIDES_LCM = `!m n r. r divides m \/ r divides n
           ==> r divides lcm(m,n)`;;

let LCM_0 = `(!n. lcm(0,n) = 0) /\ (!n. lcm(n,0) = 0)`;;

let LCM_1 = `(!n. lcm(1,n) = n) /\ (!n. lcm(n,1) = n)`;;

let LCM_SYM = `!m n. lcm(m,n) = lcm(n,m)`;;

let DIVIDES_LCM_GCD = `!m n d. d divides lcm(m,n) <=> d * gcd(m,n) divides m * n`;;

let PRIMEPOW_DIVIDES_LCM = `!m n p k.
        prime p
        ==> (p EXP k divides lcm(m,n) <=>
             p EXP k divides m \/ p EXP k divides n)`;;

let PRIME_DIVIDES_LCM = `!m n p.
        prime p
        ==> (p divides lcm(m,n) <=> p divides m \/ p divides n)`;;

let LCM_ZERO = `!m n. lcm(m,n) = 0 <=> m = 0 \/ n = 0`;;

let INDEX_LCM = `!m n p.
        prime p
        ==> index p (lcm(m,n)) =
            if m = 0 \/ n = 0 then 0
            else MAX (index p m) (index p n)`;;

let LCM_ASSOC = `!m n p. lcm(m,lcm(n,p)) = lcm(lcm(m,n),p)`;;

let LCM_REFL = `!n. lcm(n,n) = n`;;

let LCM_MULTIPLE = `!a b. lcm(b,a * b) = a * b`;;

let LCM_GCD_DISTRIB = `!a b c. lcm(a,gcd(b,c)) = gcd(lcm(a,b),lcm(a,c))`;;

let GCD_LCM_DISTRIB = `!a b c. gcd(a,lcm(b,c)) = lcm(gcd(a,b),gcd(a,c))`;;

let LCM_UNIQUE = `!d m n.
       m divides d /\ n divides d /\
       (!e. m divides e /\ n divides e ==> d divides e) <=>
       d = lcm(m,n)`;;

let LCM_EQ = `!x y u v. (!d. x divides d /\ y divides d <=> u divides d /\ v divides d)
             ==> lcm(x,y) = lcm(u,v)`;;

let LCM_EQ_1 = `!m n. lcm(m,n) = 1 <=> m = 1 /\ n = 1`;;

let DIVIDES_LCM_LEFT = `!m n. n divides m <=> lcm(m,n) = m`;;

let DIVIDES_LCM_RIGHT = `!m n. m divides n <=> lcm(m,n) = n`;;

let MULT_LCM_GCD = `!m n. lcm(m,n) * gcd(m,n) = m * n`;;

let MULT_GCD_LCM = `!m n. gcd(m,n) * lcm(m,n) = m * n`;;

let LCM_LMUL = `!a b c. lcm(c * a,c * b) = c * lcm(a,b)`;;

let LCM_RMUL = `!a b c. lcm(a * c,b * c) = c * lcm(a,b)`;;

let LCM_EXP = `!n a b. lcm(a EXP n,b EXP n) = lcm(a,b) EXP n`;;

let LCM_COPRIME_DECOMP = `!m n:num.
     ?m' n'.
        m' divides m /\ n' divides n /\ coprime(m',n') /\ m' * n' = lcm(m,n)`;;

let LE_LCM = `(!m n. m <= lcm(m,n) <=> n = 0 ==> m = 0) /\
   (!m n. n <= lcm(m,n) <=> m = 0 ==> n = 0)`;;

let LCM_LE_MULT = `!m n. lcm(m,n) <= m * n`;;

let LCM_EQ_MULT = `!m n. lcm(m,n) = m * n <=> m = 0 \/ n = 0 \/ coprime(m,n)`;;

let MAX_LE_LCM_EQ = `!m n. MAX m n <= lcm(m,n) <=> (m = 0 <=> n = 0)`;;

let MAX_LE_LCM = `!m n. (m = 0 <=> n = 0) ==> MAX m n <= lcm(m,n)`;;

(* ------------------------------------------------------------------------- *)
(* Iterated GCD and LCM over a finite set (or one with finite support).      *)
(* ------------------------------------------------------------------------- *)

let NEUTRAL_GCD = `neutral (\m n. gcd(m,n)) = 0`;;

let MONOIDAL_GCD = `monoidal (\m n:num. gcd(m,n))`;;

let NEUTRAL_LCM = `neutral (\m n. lcm(m,n)) = 1`;;

let MONOIDAL_LCM = `monoidal (\m n:num. lcm(m,n))`;;

let ITERATE_GCD_DIVIDES = `!f k i:K.
        FINITE k /\ i IN k
        ==> iterate (\m n:num. gcd(m,n)) k f divides f i`;;

let ITERATE_GCD_DIVIDES_EQ = `!f k i:K.
        i IN k
        ==> (iterate (\m n:num. gcd(m,n)) k f divides f i <=>
             FINITE {j | j IN k /\ ~(f j = 0)} \/ f i = 0)`;;

let DIVIDES_ITERATE_GCD = `!f (k:K->bool) d.
        FINITE k
        ==> (d divides iterate (\m n:num. gcd(m,n)) k f <=>
             !i. i IN k ==> d divides f i)`;;

let DIVIDES_ITERATE_GCD_GEN = `!f (k:K->bool) d.
        d divides iterate (\m n:num. gcd(m,n)) k f <=>
        FINITE {j | j IN k /\ ~(f j = 0)} ==> !i. i IN k ==> d divides f i`;;

let DIVIDES_ITERATE_LCM = `!f k i:K.
        FINITE k /\ i IN k
        ==> f i divides iterate (\m n:num. lcm(m,n)) k f`;;

let DIVIDES_ITERATE_LCM_GEN = `!f k i:K.
        i IN k
        ==> (f i divides iterate (\m n:num. lcm(m,n)) k f <=>
             FINITE {j | j IN k /\ ~(f j = 1)} \/ f i = 1)`;;

let ITERATE_LCM_DIVIDES = `!f (k:K->bool) n.
        FINITE k
        ==> (iterate (\m n:num. lcm(m,n)) k f divides n <=>
             !i. i IN k ==> f i divides n)`;;

let ITERATE_LCM_DIVIDES_GEN = `!f (k:K->bool) n.
        iterate (\m n:num. lcm(m,n)) k f divides n <=>
        FINITE {j | j IN k /\ ~(f j = 1)} ==> !i. i IN k ==> f i divides n`;;

let PRIMEPOW_DIVIDES_ITERATE_LCM = `!f (k:K->bool) p m.
        FINITE k /\ prime p
        ==> (p EXP m divides iterate (\m n:num. lcm(m,n)) k f <=>
             m = 0 \/ ?i. i IN k /\ p EXP m divides (f i))`;;

let PRIMEPOW_DIVIDES_ITERATE_LCM_GEN = `!f (k:K->bool) p m.
        prime p
        ==> (p EXP m divides iterate (\m n:num. lcm(m,n)) k f <=>
             m = 0 \/
             FINITE {j | j IN k /\ ~(f j = 1)} /\
             ?i. i IN k /\ p EXP m divides (f i))`;;

let PRIME_DIVIDES_ITERATE_LCM_GEN = `!f (k:K->bool) p.
        prime p
        ==> (p divides iterate (\m n:num. lcm(m,n)) k f <=>
             FINITE {j | j IN k /\ ~(f j = 1)} /\
             ?i. i IN k /\ p divides (f i))`;;

let PRIME_DIVIDES_ITERATE_LCM = `!f (k:K->bool) p.
        FINITE k /\ prime p
        ==> (p divides iterate (\m n:num. lcm(m,n)) k f <=>
             ?i. i IN k /\ p divides (f i))`;;

let ITERATE_LCM_EQ_0_GEN = `!(k:K->bool) f.
        iterate (\m n. lcm(m,n)) k f = 0 <=>
        FINITE {j | j IN k /\ ~(f j = 1)} /\
        ?j. j IN k /\ f j = 0`;;

let ITERATE_LCM_EQ_0 = `!(k:K->bool) f.
        FINITE k
        ==> (iterate (\m n. lcm(m,n)) k f = 0 <=>
             ?j. j IN k /\ f j = 0)`;;

let ITERATE_LCM_EQ_1_GEN = `!(k:K->bool) f.
        iterate (\m n. lcm(m,n)) k f = 1 <=>
        FINITE {j | j IN k /\ ~(f j = 1)} ==> !j. j IN k ==> f j = 1`;;

let ITERATE_LCM_EQ_1 = `!(k:K->bool) f.
        FINITE k
        ==> (iterate (\m n. lcm(m,n)) k f = 1 <=>
             !j. j IN k ==> f j = 1)`;;

let ITERATE_GCD_EQ_0_GEN = `!(k:K->bool) f.
        iterate (\m n. gcd(m,n)) k f = 0 <=>
        FINITE {j | j IN k /\ ~(f j = 0)} ==> !j. j IN k ==> f j = 0`;;

let ITERATE_GCD_EQ_0 = `!(k:K->bool) f.
        FINITE k
        ==> (iterate (\m n. gcd(m,n)) k f = 0 <=>
             !j. j IN k ==> f j = 0)`;;

(* ------------------------------------------------------------------------- *)
(* Induction principle for multiplicative functions etc.                     *)
(* ------------------------------------------------------------------------- *)

let INDUCT_COPRIME = `!P. (!a b. 1 < a /\ 1 < b /\ coprime(a,b) /\ P a /\ P b ==> P(a * b)) /\
       (!p k. prime p ==> P(p EXP k))
       ==> !n. 1 < n ==> P n`;;

let INDUCT_COPRIME_STRONG = `!P. (!a b. 1 < a /\ 1 < b /\ coprime(a,b) /\ P a /\ P b ==> P(a * b)) /\
       (!p k. prime p /\ ~(k = 0) ==> P(p EXP k))
       ==> !n. 1 < n ==> P n`;;

let INDUCT_COPRIME_ALT = `!P. P 0 /\
       (!a b. 1 < a /\ 1 < b /\ coprime(a,b) /\ P a /\ P b ==> P(a * b)) /\
       (!p k. prime p ==> P(p EXP k))
       ==> !n. P n`;;

(* ------------------------------------------------------------------------- *)
(* A conversion for divisibility.                                            *)
(* ------------------------------------------------------------------------- *)

let DIVIDES_CONV =
  let pth_0 = SPEC `b:num` DIVIDES_ZERO
  and pth_1 = prove
   (`~(a = 0) ==> (a divides b <=> (b MOD a = 0))`,
    REWRITE_TAC[DIVIDES_MOD])
  and a_tm = `a:num` and b_tm = `b:num` and zero_tm = `0`
  and dest_divides = dest_binop `(divides)` in
  fun tm ->
     let a,b = dest_divides tm in
     if a = zero_tm then
       CONV_RULE (RAND_CONV NUM_EQ_CONV) (INST [b,b_tm] pth_0)
     else
       let th1 = INST [a,a_tm; b,b_tm] pth_1 in
       let th2 = MP th1 (EQF_ELIM(NUM_EQ_CONV(rand(lhand(concl th1))))) in
       CONV_RULE (RAND_CONV (LAND_CONV NUM_MOD_CONV THENC NUM_EQ_CONV)) th2;;

(* ------------------------------------------------------------------------- *)
(* A conversion for coprimality.                                             *)
(* ------------------------------------------------------------------------- *)

let COPRIME_CONV =
  let pth_yes_l = `(m * x = n * y + 1) ==> (coprime(m,n) <=> T)`;;

(* ------------------------------------------------------------------------- *)
(* More general (slightly less efficiently coded) GCD_CONV, and LCM_CONV.    *)
(* ------------------------------------------------------------------------- *)

let GCD_CONV =
  let pth0 = `gcd(0,0) = 0`;;

let LCM_CONV =
  GEN_REWRITE_CONV I [lcm] THENC
  RATOR_CONV(LAND_CONV(LAND_CONV NUM_MULT_CONV THENC NUM_EQ_CONV)) THENC
  (GEN_REWRITE_CONV I [CONJUNCT1(SPEC_ALL COND_CLAUSES)] ORELSEC
   (GEN_REWRITE_CONV I [CONJUNCT2(SPEC_ALL COND_CLAUSES)] THENC
    COMB2_CONV (RAND_CONV NUM_MULT_CONV) GCD_CONV THENC NUM_DIV_CONV));;
