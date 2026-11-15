;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/div_Div_reciprocal_word_3by2qtvc: the verification
;; condition for computing a reciprocal approximation of a normalized
;; two-word unsigned divisor. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers in [0, 2^64) are a bijective representation of the source
;; unsigned 64-bit limbs.  The primary Why3 model uses radix 2^64.

(defun rw3-radix ()
  18446744073709551616)

(defun rw3-half-radix ()
  9223372036854775808)

(defun rw3-word-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value (rw3-radix))))

;; All divisors used by these predicates are positive under the enclosing VC
;; assumptions, so ACL2 FLOOR and MOD are the source Euclidean operations.

(defun rw3-reciprocal-p (value divisor)
  (equal
   value
   (-
    (floor
     (- (* (rw3-radix)
           (rw3-radix))
        1)
     divisor)
    (rw3-radix))))

(defun rw3-reciprocal-3by2-p
    (value high low)
  (equal
   value
   (-
    (floor
     (- (* (rw3-radix)
           (rw3-radix)
           (rw3-radix))
        1)
     (+ low
        (* (rw3-radix) high)))
    (rw3-radix))))

;; This existential Boolean is the equality-test result introduced in each
;; carry-adjustment branch of the source VC.

(defun-sk rw3-equality-choice-p
    (candidate high low product-low flag)
  (exists (equal-flag)
    (and
     (booleanp equal-flag)
     (and
      (implies
       (equal candidate high)
       (equal equal-flag t))
      (implies
       (equal equal-flag t)
       (equal candidate high)))
     (if (equal equal-flag t)
         (equal
          flag
          (if (<= low product-low)
              t
            nil))
       (equal flag nil)))))

(defun rw3-flag-premise-p
    (candidate high low product-low flag)
  (if (< high candidate)
      (equal flag t)
    (rw3-equality-choice-p
     candidate high low product-low flag)))

;; A single decrement performs the source range check and then universally
;; quantifies over the word receiving that exact mathematical value.

(defun-sk rw3-all-single-decrements-p
    (base high low)
  (forall (decremented)
    (implies
     (rw3-word-p decremented)
     (implies
      (equal decremented (- base 1))
      (rw3-reciprocal-3by2-p
       decremented high low)))))

(defun rw3-single-decrement-p
    (base high low)
  (and
   (rw3-word-p (- base 1))
   (rw3-all-single-decrements-p
    base high low)))

;; The true Boolean branch decrements twice, retaining both source range
;; checks and both universally quantified intermediate words.

(defun-sk rw3-all-first-decrements-p
    (base high low)
  (forall (first)
    (implies
     (rw3-word-p first)
     (implies
      (equal first (- base 1))
      (rw3-single-decrement-p
       first high low)))))

(defun rw3-double-decrement-p
    (base high low)
  (and
   (rw3-word-p (- base 1))
   (rw3-all-first-decrements-p
    base high low)))

(defun rw3-flag-result-p
    (flag base high low)
  (if (equal flag t)
      (rw3-double-decrement-p
       base high low)
    (rw3-single-decrement-p
     base high low)))

;; Every source Boolean satisfying the generated equality-test premise must
;; lead to the corresponding one- or two-decrement result.

(defun-sk rw3-all-flags-p
    (candidate high low product-low base)
  (forall (flag)
    (implies
     (booleanp flag)
     (implies
      (rw3-flag-premise-p
       candidate high low product-low flag)
      (rw3-flag-result-p
       flag base high low)))))

(defun rw3-after-high-addition-p
    (candidate product-high product-low base high low)
  (if (< candidate product-high)
      (rw3-all-flags-p
       candidate high low product-low base)
    (rw3-reciprocal-3by2-p
     base high low)))

;; This is the common multiplication-and-carry continuation.  PRODUCT-LOW
;; and PRODUCT-HIGH are the universally quantified words whose base-radix
;; value equals BASE * LOW; ADJUSTED is the modular high-word addition.

(defun-sk rw3-product-continuation-p
    (remainder base high low)
  (forall (product-low product-high adjusted)
    (implies
     (and
      (rw3-word-p product-low)
      (rw3-word-p product-high)
      (rw3-word-p adjusted))
     (implies
      (equal
       (+ product-low
          (* (rw3-radix) product-high))
       (* base low))
      (implies
       (equal
        adjusted
        (mod
         (+ remainder product-high)
         (rw3-radix)))
       (rw3-after-high-addition-p
        adjusted product-high product-low
        base high low))))))

;; When the first modular addition carries but its residue is below HIGH, the
;; quotient is decremented once before multiplying by LOW.

(defun-sk rw3-branch-b-continuation-p
    (base residue high low)
  (forall (decremented reduced-residue)
    (implies
     (and
      (rw3-word-p decremented)
      (rw3-word-p reduced-residue))
     (implies
      (equal decremented (- base 1))
      (implies
       (equal
        reduced-residue
        (mod (- residue high)
             (rw3-radix)))
       (rw3-product-continuation-p
        reduced-residue
        decremented
        high
        low))))))

(defun rw3-branch-b-p
    (base residue high low)
  (and
   (rw3-word-p (- base 1))
   (rw3-branch-b-continuation-p
    base residue high low)))

;; When the carried residue is at least HIGH, the source decrements the
;; quotient, subtracts HIGH without wrap, decrements again, then performs one
;; modular subtraction of HIGH before the common multiplication continuation.

(defun-sk rw3-branch-a-after-subtraction-p
    (first first-residue high low)
  (forall (second reduced-residue)
    (implies
     (and
      (rw3-word-p second)
      (rw3-word-p reduced-residue))
     (implies
      (equal second (- first 1))
      (implies
       (equal
        reduced-residue
        (mod (- first-residue high)
             (rw3-radix)))
       (rw3-product-continuation-p
        reduced-residue
        second
        high
        low))))))

(defun rw3-branch-a-after-first-residue-p
    (first first-residue high low)
  (and
   (rw3-word-p (- first 1))
   (rw3-branch-a-after-subtraction-p
    first first-residue high low)))

(defun-sk rw3-branch-a-first-residue-p
    (residue first high low)
  (forall (first-residue)
    (implies
     (rw3-word-p first-residue)
     (implies
      (equal first-residue
             (- residue high))
      (rw3-branch-a-after-first-residue-p
       first first-residue high low)))))

(defun rw3-branch-a-after-first-p
    (residue first high low)
  (and
   (rw3-word-p (- residue high))
   (rw3-branch-a-first-residue-p
    residue first high low)))

(defun-sk rw3-branch-a-continuation-p
    (base residue high low)
  (forall (first)
    (implies
     (rw3-word-p first)
     (implies
      (equal first (- base 1))
      (rw3-branch-a-after-first-p
       residue first high low)))))

(defun rw3-branch-a-p
    (base residue high low)
  (and
   (rw3-word-p (- base 1))
   (rw3-branch-a-continuation-p
    base residue high low)))

(defun rw3-residue-case-p
    (base residue high low)
  (if (< residue low)
      (if (<= high residue)
          (rw3-branch-a-p
           base residue high low)
        (rw3-branch-b-p
         base residue high low))
    (rw3-product-continuation-p
     residue base high low)))

;; These three predicates preserve the source nesting of the universally
;; quantified reciprocal, product residue, and sum residue words.

(defun-sk rw3-all-sum-residues-p
    (base product-residue high low)
  (forall (sum-residue)
    (implies
     (rw3-word-p sum-residue)
     (implies
      (equal
       sum-residue
       (mod (+ product-residue low)
            (rw3-radix)))
      (rw3-residue-case-p
       base sum-residue high low)))))

(defun-sk rw3-all-product-residues-p
    (base high low)
  (forall (product-residue)
    (implies
     (rw3-word-p product-residue)
     (implies
      (equal
       product-residue
       (mod (* high base)
            (rw3-radix)))
      (rw3-all-sum-residues-p
       base product-residue high low)))))

(defun-sk rw3-all-reciprocals-p
    (high low)
  (forall (base)
    (implies
     (rw3-word-p base)
     (implies
      (rw3-reciprocal-p base high)
      (rw3-all-product-residues-p
       base high low)))))

;; The theorem parameters HIGH and LOW remain universally quantified.  The
;; normalized-high assumption and its repeated first conclusion conjunct are
;; both retained exactly from the verification condition.

(defun-sk
    ntp4vc-pearl-multiprecision-div-reciprocal-word-3by2qtvc-statement
    ()
  (forall (high low)
    (implies
     (and
      (rw3-word-p high)
      (rw3-word-p low))
     (implies
      (<= (rw3-half-radix) high)
      (and
       (<= (rw3-half-radix) high)
       (rw3-all-reciprocals-p
        high low))))))

(value-triple :itpeval-statement-checked)
:q
