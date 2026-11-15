(* ========================================================================= *)
(* Rob Arthan's "Descartes's Rule of Signs by an Easy Induction".            *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* A couple of handy lemmas.                                                 *)
(* ------------------------------------------------------------------------- *)

let OPPOSITE_SIGNS = `!a b:real. a * b < &0 <=> &0 < a /\ b < &0 \/ a < &0 /\ &0 < b`;;

let VARIATION_SET_FINITE = `FINITE s ==> FINITE {p,q | p IN s /\ q IN s /\ P p q}`;;

(* ------------------------------------------------------------------------- *)
(* Variation in a sequence of coefficients.                                  *)
(* ------------------------------------------------------------------------- *)

let variation = new_definition
 `variation s (a:num->real) =
     CARD {(p,q) | p IN s /\ q IN s /\ p < q /\
                   a(p) * a(q) < &0 /\
                   !i. i IN s /\ p < i /\ i < q ==> a(i) = &0 }`;;

let VARIATION_EQ = `!a b s. (!i. i IN s ==> a i = b i) ==> variation s a = variation s b`;;

let VARIATION_SUBSET = `!a s t. t SUBSET s /\ (!i. i IN (s DIFF t) ==> a i = &0)
           ==> variation s a = variation t a`;;

let VARIATION_SPLIT = `!a s n.
        FINITE s /\ n IN s /\ ~(a n = &0)
        ==> variation s a = variation {i | i IN s /\ i <= n} a +
                            variation {i | i IN s /\ n <= i} a`;;

let VARIATION_SPLIT_NUMSEG = `!a m n p. n IN m..p /\ ~(a n = &0)
             ==> variation(m..p) a = variation(m..n) a + variation(n..p) a`;;

let VARIATION_1 = `!a n. variation {n} a = 0`;;

let VARIATION_2 = `!a m n. variation {m,n} a = if a(m) * a(n) < &0 then 1 else 0`;;

let VARIATION_3 = `!a m n p.
        m < n /\ n < p
        ==> variation {m,n,p} a = if a(n) = &0 then variation{m,p} a
                                  else variation {m,n} a + variation{n,p} a`;;

let VARIATION_OFFSET = `!p m n a. variation(m+p..n+p) a = variation(m..n) (\i. a(i + p))`;;

(* ------------------------------------------------------------------------- *)
(* The crucial lemma (roughly Lemma 2 in the paper).                         *)
(* ------------------------------------------------------------------------- *)

let ARTHAN_LEMMA = `!n a b.
        ~(a n = &0) /\ (b n = &0) /\ (!m. sum(0..m) a = b m)
        ==> ?d. ODD d /\ variation (0..n) a = variation (0..n) b + d`;;

(* ------------------------------------------------------------------------- *)
(* Relate even-ness or oddity of variation to signs of end coefficients.     *)
(* ------------------------------------------------------------------------- *)

let VARIATION_OPPOSITE_ENDS = `!a m n.
    m <= n /\ ~(a m = &0) /\ ~(a n = &0)
    ==> (ODD(variation(m..n) a) <=> a m * a n < &0)`;;

(* ------------------------------------------------------------------------- *)
(* Polynomial with odd variation has at least one positive root.             *)
(* This is the only "analytical" part of the proof.                          *)
(* ------------------------------------------------------------------------- *)

let REAL_POLYFUN_SGN_AT_INFINITY = `!a n. ~(a n = &0)
         ==> ?B. &0 < B /\
                 !x. B <= abs x
                     ==> real_sgn(sum(0..n) (\i. a i * x pow i)) =
                         real_sgn(a n * x pow n)`;;

let REAL_POLYFUN_HAS_POSITIVE_ROOT = `!a n. a 0 < &0 /\ &0 < a n
         ==> ?x. &0 < x /\ sum(0..n) (\i. a i * x pow i) = &0`;;

let ODD_VARIATION_POSITIVE_ROOT = `!a n. ODD(variation(0..n) a)
         ==> ?x. &0 < x /\ sum(0..n) (\i. a i * x pow i) = &0`;;

(* ------------------------------------------------------------------------- *)
(* Define root multiplicities.                                               *)
(* ------------------------------------------------------------------------- *)

let multiplicity = new_definition
 `multiplicity f r =
        @k. ?a n. ~(sum(0..n) (\i. a i * r pow i) = &0) /\
                  !x. f(x) = (x - r) pow k * sum(0..n) (\i. a i * x pow i)`;;

let MULTIPLICITY_UNIQUE = `!f a r b m k.
        (!x. f(x) = (x - r) pow k * sum(0..m) (\j. b j * x pow j)) /\
        ~(sum(0..m) (\j. b j * r pow j) = &0)
        ==> k = multiplicity f r`;;

let MULTIPLICITY_WORKS = `!r n a.
    (?i. i IN 0..n /\ ~(a i = &0))
    ==> ?b m.
        ~(sum(0..m) (\i. b i * r pow i) = &0) /\
        !x. sum(0..n) (\i. a i * x pow i) =
            (x - r) pow multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r *
            sum(0..m) (\i. b i * x pow i)`;;

let MULTIPLICITY_OTHER_ROOT = `!a n r s.
    ~(r = s) /\ (?i. i IN 0..n /\ ~(a i = &0))
     ==> multiplicity (\x. (x - r) pow m * sum(0..n) (\i. a i * x pow i)) s =
         multiplicity (\x.  sum(0..n) (\i. a i * x pow i)) s`;;

(* ------------------------------------------------------------------------- *)
(* The main lemmas to be applied iteratively.                                *)
(* ------------------------------------------------------------------------- *)

let VARIATION_POSITIVE_ROOT_FACTOR = `!a n r.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b. ~(b(n - 1) = &0) /\
            (!x. sum(0..n) (\i. a i * x pow i) =
                 (x - r) * sum(0..n-1) (\i. b i * x pow i)) /\
            ?d. ODD d /\ variation(0..n) a = variation(0..n-1) b + d`;;

let VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR = `!r n a.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b k m. 0 < k /\ m < n /\ ~(b m = &0) /\
                (!x. sum(0..n) (\i. a i * x pow i) =
                     (x - r) pow k * sum(0..m) (\i. b i * x pow i)) /\
                ~(sum(0..m) (\j. b j * r pow j) = &0) /\
                ?d. EVEN d /\ variation(0..n) a = variation(0..m) b + k + d`;;

let VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR = `!r n a.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b m. m < n /\ ~(b m = &0) /\
              (!x. sum(0..n) (\i. a i * x pow i) =
                   (x - r) pow
                   (multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r) *
                   sum(0..m) (\i. b i * x pow i)) /\
              ~(sum(0..m) (\j. b j * r pow j) = &0) /\
              ?d. EVEN d /\
                  variation(0..n) a = variation(0..m) b +
                     multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r + d`;;

(* ------------------------------------------------------------------------- *)
(* Hence the main theorem.                                                   *)
(* ------------------------------------------------------------------------- *)

let DESCARTES_RULE_OF_SIGNS = `!f a n. f = (\x. sum(0..n) (\i. a i * x pow i)) /\
           (?i. i IN 0..n /\ ~(a i = &0))
           ==> ?d. EVEN d /\
                   variation(0..n) a =
                   nsum {r | &0 < r /\ f(r) = &0} (\r. multiplicity f r) + d`;;
