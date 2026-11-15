(* ========================================================================= *)
(* Dirichlet's theorem.                                                      *)
(* ========================================================================= *)

needs "Library/products.ml";;
needs "Library/agm.ml";;
needs "Multivariate/transcendentals.ml";;
needs "Library/pocklington.ml";;
needs "Library/multiplicative.ml";;
needs "Examples/mangoldt.ml";;

prioritize_real();;
prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Rearranging a certain kind of double sum.                                 *)
(* ------------------------------------------------------------------------- *)

let VSUM_VSUM_DIVISORS = `!f x. vsum (1..x) (\n. vsum {d | d divides n} (f n)) =
         vsum (1..x) (\n. vsum (1..(x DIV n)) (\k. f (k * n) n))`;;

(* ------------------------------------------------------------------------- *)
(* Useful approximation lemmas.                                              *)
(* ------------------------------------------------------------------------- *)

let REAL_EXP_1_LE_4 = `exp(&1) <= &4`;;

let DECREASING_LOG_OVER_N = `!n. 4 <= n ==> log(&n + &1) / (&n + &1) <= log(&n) / &n`;;

(* ------------------------------------------------------------------------- *)
(* An ad-hoc fact about complex n'th roots.                                  *)
(* ------------------------------------------------------------------------- *)

let EXISTS_COMPLEX_ROOT_NONTRIVIAL = `!a n. 2 <= n ==> ?z. z pow n = a /\ ~(z = Cx(&1))`;;

(* ------------------------------------------------------------------------- *)
(* Definition of a Dirichlet character mod d.                                *)
(* ------------------------------------------------------------------------- *)

let dirichlet_character = new_definition
 `dirichlet_character d (c:num->complex) <=>
        (!n. c(n + d) = c(n)) /\
        (!n. c(n) = Cx(&0) <=> ~coprime(n,d)) /\
        (!m n. c(m * n) = c(m) * c(n))`;;

let DIRICHLET_CHARACTER_PERIODIC = `!d c n. dirichlet_character d c ==> c(n + d) = c(n)`;;

let DIRICHLET_CHARACTER_EQ_0 = `!d c n. dirichlet_character d c ==> (c(n) = Cx(&0) <=> ~coprime(n,d))`;;

let DIRICHLET_CHARACTER_MUL = `!d c m n. dirichlet_character d c ==> c(m * n) = c(m) * c(n)`;;

let DIRICHLET_CHARACTER_EQ_1 = `!d c. dirichlet_character d c ==> c(1) = Cx(&1)`;;

let DIRICHLET_CHARACTER_POW = `!d c m n. dirichlet_character d c ==> c(m EXP n) = c(m) pow n`;;

let DIRICHLET_CHARACTER_PERIODIC_GEN = `!d c m n. dirichlet_character d c ==> c(m * d + n) = c(n)`;;

let DIRICHLET_CHARACTER_CONG = `!d c m n.
        dirichlet_character d c /\ (m == n) (mod d) ==> c(m) = c(n)`;;

let DIRICHLET_CHARACTER_ROOT = `!d c n. dirichlet_character d c /\ coprime(d,n)
           ==> c(n) pow phi(d) = Cx(&1)`;;

let DIRICHLET_CHARACTER_NORM = `!d c n. dirichlet_character d c
           ==> norm(c n) = if coprime(d,n) then &1 else &0`;;

(* ------------------------------------------------------------------------- *)
(* The principal character mod d.                                            *)
(* ------------------------------------------------------------------------- *)

let chi_0 = new_definition
 `chi_0 d n = if coprime(n,d) then Cx(&1) else Cx(&0)`;;

let DIRICHLET_CHARACTER_CHI_0 = `dirichlet_character d (chi_0 d)`;;

let DIRICHLET_CHARACTER_EQ_PRINCIPAL = `!d c. dirichlet_character d c
         ==> (c = chi_0 d <=> !n. coprime(n,d) ==> c(n) = Cx(&1))`;;

let DIRICHLET_CHARACTER_NONPRINCIPAL = `!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ?n. coprime(n,d) /\ ~(c n = Cx(&0)) /\ ~(c n = Cx(&1))`;;

let DIRICHLET_CHARACTER_0 = `!c. dirichlet_character 0 c <=> c = chi_0 0`;;

let DIRICHLET_CHARACTER_1 = `!c. dirichlet_character 1 c <=> !n. c n = Cx(&1)`;;

let DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL = `!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ~(d = 0) /\ ~(d = 1)`;;

let DIRICHLET_CHARACTER_ZEROSUM = `!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> vsum(1..d) c = Cx(&0)`;;

let DIRICHLET_CHARACTER_ZEROSUM_MUL = `!d c n. dirichlet_character d c /\ ~(c = chi_0 d)
           ==> vsum(1..d*n) c = Cx(&0)`;;

let DIRICHLET_CHARACTER_SUM_MOD = `!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> vsum(1..n) c = vsum(1..(n MOD d)) c`;;

(* ------------------------------------------------------------------------- *)
(* Finiteness of the set of characters (later we could get size =  phi(d)).  *)
(* ------------------------------------------------------------------------- *)

let FINITE_DIRICHLET_CHARACTERS = `!d. FINITE {c | dirichlet_character d c}`;;

(* ------------------------------------------------------------------------- *)
(* Very basic group structure.                                               *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET_CHARACTER_MUL_CNJ = `!d c n. dirichlet_character d c /\ ~(c n = Cx(&0))
           ==> cnj(c n) * c n = Cx(&1) /\ c n * cnj(c n) = Cx(&1)`;;

let DIRICHLET_CHARACTER_CNJ = `!d c. dirichlet_character d c ==> dirichlet_character d (\n. cnj(c n))`;;

let DIRICHLET_CHARACTER_GROUPMUL = `!d c1 c2. dirichlet_character d c1 /\ dirichlet_character d c2
             ==> dirichlet_character d (\n. c1(n) * c2(n))`;;

let DIRICHLET_CHARACTER_GROUPINV = `!d c. dirichlet_character d c ==> (\n. cnj(c n) * c n) = chi_0 d`;;

(* ------------------------------------------------------------------------- *)
(* Orthogonality relations, a weak version of one first.                     *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET_CHARACTER_SUM_OVER_NUMBERS = `!d c. dirichlet_character d c
         ==> vsum (1..d) c = if c = chi_0 d then Cx(&(phi d)) else Cx(&0)`;;

let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK = `!d n. vsum {c | dirichlet_character d c} (\x. x n) = Cx(&0) \/
         coprime(n,d) /\ !c. dirichlet_character d c ==> c(n) = Cx(&1)`;;

let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS = `!d n. real(vsum {c | dirichlet_character d c} (\c. c n)) /\
         &0 <= Re(vsum {c | dirichlet_character d c} (\c. c n))`;;

(* ------------------------------------------------------------------------- *)
(* A somewhat gruesome lemma about extending a character from a subgroup.    *)
(* ------------------------------------------------------------------------- *)

let CHARACTER_EXTEND_FROM_SUBGROUP = `!f h a d.
        h SUBSET {x | x < d /\ coprime(x,d)} /\
        (1 IN h) /\
        (!x y. x IN h /\ y IN h ==> ((x * y) MOD d) IN h) /\
        (!x. x IN h ==> ?y. y IN h /\ (x * y == 1) (mod d)) /\
        (!x. x IN h ==> ~(f x = Cx(&0))) /\
        (!x y. x IN h /\ y IN h
                 ==> f((x * y) MOD d) = f(x) * f(y)) /\
        a IN {x | x < d /\ coprime(x,d)} DIFF h
        ==> ?f' h'. (a INSERT h) SUBSET h' /\
                    h' SUBSET {x | x < d /\ coprime(x,d)} /\
                    (!x. x IN h ==> f'(x) = f(x)) /\
                    ~(f' a = Cx(&1)) /\
                    1 IN h' /\
                    (!x y. x IN h' /\ y IN h' ==> ((x * y) MOD d) IN h') /\
                    (!x. x IN h' ==> ?y. y IN h' /\ (x * y == 1) (mod d)) /\
                    (!x. x IN h' ==> ~(f' x = Cx(&0))) /\
                    (!x y. x IN h' /\ y IN h'
                           ==> f'((x * y) MOD d) = f'(x) * f'(y))`;;

(* ------------------------------------------------------------------------- *)
(* Hence the key result that we can find a distinguishing character.         *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET_CHARACTER_DISCRIMINATOR = `!d n. 1 < d /\ ~((n == 1) (mod d))
          ==> ?c. dirichlet_character d c /\ ~(c n = Cx(&1))`;;

(* ------------------------------------------------------------------------- *)
(* Hence we get the full second orthogonality relation.                      *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT = `!d n. vsum {c | dirichlet_character d c} (\c. c n) =
                if (n == 1) (mod d)
                then Cx(&(CARD {c | dirichlet_character d c}))
                else Cx(&0)`;;

let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS = `!d n. 1 <= d
         ==> vsum {c | dirichlet_character d c} (\c. c(n)) =
                if (n == 1) (mod d) then Cx(&(phi d)) else Cx(&0)`;;

(* ------------------------------------------------------------------------- *)
(* L-series, just at the point s = 1.                                        *)
(* ------------------------------------------------------------------------- *)

let Lfunction_DEF = new_definition
 `Lfunction c = infsum (from 1) (\n. c(n) / Cx(&n))`;;

let BOUNDED_LFUNCTION_PARTIAL_SUMS = `!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> bounded {vsum (1..n) c | n IN (:num)}`;;

let LFUNCTION = `!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ((\n. c(n) / Cx(&n)) sums (Lfunction c)) (from 1)`;;

(* ------------------------------------------------------------------------- *)
(* Other properties of conjugate characters.                                 *)
(* ------------------------------------------------------------------------- *)

let CNJ_CHI_0 = `!d n. cnj(chi_0 d n) = chi_0 d n`;;

let LFUNCTION_CNJ = `!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> Lfunction (\n. cnj(c n)) = cnj(Lfunction c)`;;

(* ------------------------------------------------------------------------- *)
(* Explicit bound on truncating the Lseries.                                 *)
(* ------------------------------------------------------------------------- *)

let LFUNCTION_PARTIAL_SUM = `!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ?B. &0 < B /\
                 !n. 1 <= n
                     ==> norm(Lfunction c - vsum(1..n) (\n. c(n) / Cx(&n)))
                          <= B / (&n + &1)`;;

let LFUNCTION_PARTIAL_SUM_STRONG = `!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ?B. &0 < B /\
                 !n. norm(Lfunction c - vsum(1..n) (\n. c(n) / Cx(&n)))
                         <= B / (&n + &1)`;;

(* ------------------------------------------------------------------------- *)
(* First key bound, when the Lfunction is not zero (as indeed it isn't).     *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA = `!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> bounded
              { Lfunction(c) *
                vsum(1..x) (\n. c(n) * Cx(mangoldt n / &n)) -
                vsum(1..x) (\n. c(n) * Cx(log(&n) / &n)) | x IN (:num)}`;;

let SUMMABLE_CHARACTER_LOG_OVER_N = `!c d. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> summable (from 1) (\n. c(n) * Cx(log(&n) / &n))`;;

let BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT = `!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> bounded
              { Lfunction(c) *
                vsum(1..x) (\n. c(n) * Cx(mangoldt n / &n)) | x IN (:num)}`;;

let BOUNDED_DIRICHLET_MANGOLDT_NONZERO = `!d c.
      dirichlet_character d c /\ ~(c = chi_0 d) /\ ~(Lfunction c = Cx(&0))
      ==> bounded { vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) | x IN (:num)}`;;

(* ------------------------------------------------------------------------- *)
(* Now a bound when the Lfunction is zero (hypothetically).                  *)
(* ------------------------------------------------------------------------- *)

let MANGOLDT_LOG_SUM = `!n. 1 <= n
       ==> mangoldt(n) = --(sum {d | d divides n} (\d. mobius(d) * log(&d)))`;;

let BOUNDED_DIRICHLET_MANGOLDT_LEMMA = `!d c x.
        dirichlet_character d c /\ ~(c = chi_0 d) /\ 1 <= x
        ==> Cx(log(&x)) + vsum (1..x) (\n. c(n) * Cx(mangoldt n / &n)) =
            vsum (1..x) (\n. c(n) / Cx(&n) *
                             vsum {d | d divides n}
                                  (\d. Cx(mobius(d) * log(&x / &d))))`;;

let SUM_LOG_OVER_X_BOUND = `!x. abs(sum(1..x) (\n. log(&x / &n) / &x)) <= &4`;;

let BOUNDED_DIRICHLET_MANGOLDT_ZERO = `!d c.
      dirichlet_character d c /\ ~(c = chi_0 d) /\ Lfunction c = Cx(&0)
      ==> bounded { vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) +
                    Cx(log(&x)) | x IN (:num)}`;;

(* ------------------------------------------------------------------------- *)
(* Now the analogous result for the principal character.                     *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA = `!d. 1 <= d
       ==> norm(vsum(1..x) (\n. (chi_0 d n - Cx(&1)) * Cx(mangoldt n / &n)))
            <= sum {p | prime p /\ p divides d} (\p. log(&p))`;;

let BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL = `!d. 1 <= d
       ==> bounded { vsum(1..x) (\n. chi_0 d n * Cx(mangoldt n / &n)) -
                     Cx(log(&x)) | x IN (:num)}`;;

(* ------------------------------------------------------------------------- *)
(* The arithmetic-geometric mean that we want.                               *)
(* ------------------------------------------------------------------------- *)

let SUM_OF_NUMBERS = `!n. nsum(0..n) (\i. i) = (n * (n + 1)) DIV 2`;;

let PRODUCT_POW_NSUM = `!s. FINITE s ==> product s (\i. z pow (f i)) = z pow (nsum s f)`;;

let PRODUCT_SPECIAL = `!z i. product (0..n) (\i. z pow i) = z pow ((n * (n + 1)) DIV 2)`;;

let AGM_SPECIAL = `!n t. &0 <= t
         ==> (&n + &1) pow 2 * t pow n <= (sum(0..n) (\k. t pow k)) pow 2`;;

(* ------------------------------------------------------------------------- *)
(* The trickiest part: the nonvanishing of L-series for real character.      *)
(* Proof from Monsky's article (AMM 1993, pp. 861-2).                        *)
(* ------------------------------------------------------------------------- *)

let DIVISORSUM_PRIMEPOW = `!f p k. prime p
           ==> sum {m | m divides (p EXP k)} c = sum(0..k) (\i. c(p EXP i))`;;

let DIVISORVSUM_PRIMEPOW = `!f p k. prime p
           ==> vsum {m | m divides (p EXP k)} c = vsum(0..k) (\i. c(p EXP i))`;;

let DIRICHLET_CHARACTER_DIVISORSUM_EQ_1 = `!d c p k. dirichlet_character d c /\ prime p /\ p divides d
             ==> vsum {m | m divides (p EXP k)} c = Cx(&1)`;;

let DIRICHLET_CHARACTER_REAL_CASES = `!d c. dirichlet_character d c /\ (!n. real(c n))
         ==> !n. c n = --Cx(&1) \/ c n = Cx(&0) \/ c n = Cx(&1)`;;

let DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS = `!d c p k. dirichlet_character d c /\ (!n. real(c n)) /\ prime p
             ==> &0 <= Re(vsum {m | m divides (p EXP k)} c)`;;

let DIRICHLET_CHARACTER_DIVISORSUM_POS = `!d c n. dirichlet_character d c /\ (!n. real(c n)) /\ ~(n = 0)
           ==> &0 <= Re(vsum {m | m divides n} c)`;;

let lemma = `!x n. &0 <= x /\ x <= &1 ==> &1 - &n * x <= (&1 - x) pow n`;;

let LFUNCTION_NONZERO_REAL = `!d c. dirichlet_character d c /\ ~(c = chi_0 d) /\ (!n. real(c n))
         ==> ~(Lfunction c = Cx(&0))`;;

(* ------------------------------------------------------------------------- *)
(* Deduce nonvanishing of all the nonprincipal characters.                   *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_DIFF_LOGMUL = `!f a. bounded {f x - Cx(log(&x)) * a | x IN (:num)}
         ==> (!x. &0 <= Re(f x)) ==> &0 <= Re a`;;

let LFUNCTION_NONZERO_NONPRINCIPAL = `!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ~(Lfunction c = Cx(&0))`;;

(* ------------------------------------------------------------------------- *)
(* Hence derive our boundedness result for all nonprincipal characters.      *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL = `!d c.
      dirichlet_character d c /\ ~(c = chi_0 d)
      ==> bounded { vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) | x IN (:num)}`;;

(* ------------------------------------------------------------------------- *)
(* Hence the main sum result.                                                *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS = `!d l. 1 <= d /\ coprime(l,d)
         ==> bounded { vsum {c | dirichlet_character d c}
                            (\c. c(l) *
                                 vsum(1..x) (\n. c n * Cx (mangoldt n / &n))) -
                       Cx(log(&x)) | x IN (:num)}`;;

let DIRICHLET_MANGOLDT = `!d k. 1 <= d /\ coprime(k,d)
         ==> bounded { Cx(&(phi d)) * vsum {n | n IN 1..x /\ (n == k) (mod d)}
                                           (\n. Cx(mangoldt n / &n)) -
                       Cx(log(&x)) | x IN (:num)}`;;

let DIRICHLET_MANGOLDT_EXPLICIT = `!d k. 1 <= d /\ coprime (k,d)
         ==> ?B. &0 < B /\
                 !x. abs(sum {n | n IN 1..x /\ (n == k) (mod d)}
                             (\n. mangoldt n / &n) -
                         log(&x) / &(phi d)) <= B`;;

let DIRICHLET_STRONG = `!d k. 1 <= d /\ coprime(k,d)
         ==> ?B. &0 < B /\
                 !x. abs(sum {p | p IN 1..x /\ prime p /\ (p == k) (mod d)}
                             (\p. log(&p) / &p) -
                         log(&x) / &(phi d)) <= B`;;

(* ------------------------------------------------------------------------- *)
(* Ignore the density details and prove the main result.                     *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET = `!d k. 1 <= d /\ coprime(k,d)
         ==> INFINITE {p | prime p /\ (p == k) (mod d)}`;;
