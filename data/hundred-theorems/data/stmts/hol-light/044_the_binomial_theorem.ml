(* ========================================================================= *)
(* Binomial coefficients and the binomial theorem.                           *)
(* ========================================================================= *)

let binom = define
  `(!n. binom(n,0) = 1) /\
   (!k. binom(0,SUC(k)) = 0) /\
   (!n k. binom(SUC(n),SUC(k)) = binom(n,SUC(k)) + binom(n,k))`;;

let BINOM_0 = `!n. binom(0,n) = if n = 0 then 1 else 0`;;

let BINOM_LT = `!n k. n < k ==> binom(n,k) = 0`;;

let BINOM_REFL = `!n. binom(n,n) = 1`;;

let BINOM_1 = `!n. binom(n,1) = n`;;

let BINOM_FACT = `!n k. FACT n * FACT k * binom(n+k,k) = FACT(n + k)`;;

let BINOM_EQ_0 = `!n k. binom(n,k) = 0 <=> n < k`;;

let BINOM_PENULT = `!n. binom(SUC n,n) = SUC n`;;

let BINOM_GE_TOP = `!m n. 1 <= m /\ m < n ==> n <= binom(n,m)`;;

(* ------------------------------------------------------------------------- *)
(* More potentially useful lemmas.                                           *)
(* ------------------------------------------------------------------------- *)

let BINOM_TOP_STEP = `!n k. ((n + 1) - k) * binom(n + 1,k) = (n + 1) * binom(n,k)`;;

let BINOM_BOTTOM_STEP = `!n k. (k + 1) * binom(n,k + 1) = (n - k) * binom(n,k)`;;

(* ------------------------------------------------------------------------- *)
(* The "number of combinations", number of size-m subsets of a size-n set.   *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_RESTRICTED_POWERSET = `!n m s:A->bool.
        s HAS_SIZE n ==> {t | t SUBSET s /\ t HAS_SIZE m} HAS_SIZE binom(n,m)`;;

let CARD_RESTRICTED_POWERSET = `!s k. FINITE s ==> CARD {t | t SUBSET s /\ t HAS_SIZE k} = binom(CARD s,k)`;;

(* ------------------------------------------------------------------------- *)
(* Binomial expansion.                                                       *)
(* ------------------------------------------------------------------------- *)

let BINOMIAL_THEOREM = `!n x y.
      (x + y) EXP n = nsum(0..n) (\k. binom(n,k) * x EXP k * y EXP (n - k))`;;

(* ------------------------------------------------------------------------- *)
(* Same thing for the reals.                                                 *)
(* ------------------------------------------------------------------------- *)

let REAL_BINOMIAL_THEOREM = `!n x y.
     (x + y) pow n = sum(0..n) (\k. &(binom(n,k)) * x pow k * y pow (n - k))`;;

(* ------------------------------------------------------------------------- *)
(* More direct stepping theorems over the reals.                             *)
(* ------------------------------------------------------------------------- *)

let BINOM_TOP_STEP_REAL = `!n k. &(binom(n + 1,k)):real =
           if k = n + 1 then &1
           else (&n + &1) / (&n + &1 - &k) * &(binom(n,k))`;;

let BINOM_BOTTOM_STEP_REAL = `!n k. &(binom(n,k+1)):real = (&n - &k) / (&k + &1) * &(binom(n,k))`;;

let REAL_OF_NUM_BINOM = `!n k. &(binom(n,k)):real =
             if k <= n then &(FACT n) / (&(FACT(n - k)) * &(FACT k))
             else &0`;;

(* ------------------------------------------------------------------------- *)
(* Some additional theorems for stepping both arguments together.            *)
(* ------------------------------------------------------------------------- *)

let BINOM_BOTH_STEP_REAL = `!p k. &(binom(p + 1,k + 1)):real = (&p + &1) / (&k + &1) * &(binom(p,k))`;;

let BINOM_BOTH_STEP = `!p k. (k + 1) * binom(p + 1,k + 1) = (p + 1) * binom(p,k)`;;

let BINOM_BOTH_STEP_DOWN = `!p k. (k = 0 ==> p = 0) ==> k * binom(p,k) = p * binom(p - 1,k - 1)`;;

let BINOM = `!n k. binom(n,k) =
            if k <= n then FACT(n) DIV (FACT(n - k) * FACT(k))
            else 0`;;

let DIVIDES_GCD_BINOM = `!n k. n divides gcd(n,k) * binom(n,k)`;;

let DIVIDES_COPRIME_BINOM = `!n k. coprime(n,k) ==> n divides binom (n,k)`;;

let DIVIDES_PRIME_BINOM = `!n p. prime p /\ 0 < n /\ n < p ==> p divides binom(p,n)`;;

(* ------------------------------------------------------------------------- *)
(* Additional lemmas.                                                        *)
(* ------------------------------------------------------------------------- *)

let BINOM_SYM = `!n k. binom(n,n-k) = if k <= n then binom(n,k) else 1`;;

let BINOM_MUL_SHIFT = `!m n k. k <= m
           ==> binom(n,m) * binom(m,k) = binom(n,k) * binom(n - k,m - k)`;;

let APPELL_SEQUENCE = `!c n x y. sum (0..n)
               (\k.  &(binom(n,k)) *
                     sum(0..k)
                        (\l. &(binom(k,l)) * c l * x pow (k - l)) *
                     y pow (n - k)) =
           sum (0..n) (\k. &(binom(n,k)) * c k * (x + y) pow (n - k))`;;

(* ------------------------------------------------------------------------- *)
(* Numerical computation of binom.                                           *)
(* ------------------------------------------------------------------------- *)

let NUM_BINOM_CONV =
  let pth_step = `binom(n,k) = y
     ==> k <= n
         ==> (SUC n) * y = ((n + 1) - k) * x ==> binom(SUC n,k) = x`;;
