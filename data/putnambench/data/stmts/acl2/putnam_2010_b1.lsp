;; Statement-only formalization of PutnamBench corpus artifact putnam_2010_b1:
;; no real sequence has m-th power series summing to m for every positive
;; integer m. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The conservative generic symbol supplies a rational regular Cauchy name
;; for a_i at every natural index i. It is arbitrary, not a rational-valued
;; sequence or a finite table. Every real sequence admits such names, and
;; every symbol satisfying PUTNAM-2010-B1-REGULAR-REAL-SEQUENCE-NAME-P
;; determines a unique real sequence.
;;
;; Since the requested answer is false, negating the source existential gives
;; the equivalent universal statement that every such sequence fails the
;; power-series condition. DEFSTUB represents that arbitrary sequence, while
;; all scalar quantifiers and convergence witnesses remain internal DEFUN-SK
;; quantifiers.

(defstub putnam-2010-b1-sequence-approx (index precision) t)

(defun putnam-2010-b1-positive-rational-p (x)
  (and
   (rationalp x)
   (< 0 x)))

(defun-sk putnam-2010-b1-regular-real-sequence-name-p ()
  (forall (index epsilon eta)
    (implies
     (and
      (natp index)
      (putnam-2010-b1-positive-rational-p epsilon)
      (putnam-2010-b1-positive-rational-p eta))
     (let ((left
            (putnam-2010-b1-sequence-approx index epsilon))
           (right
            (putnam-2010-b1-sequence-approx index eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

;; This is the rational approximation, at a common precision, to the first
;; TERMS entries of the real series sum_i (a_i)^EXPONENT.

(defun putnam-2010-b1-partial-power-sum
    (exponent terms precision)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- (nfix terms) 1)))
      (+
       (putnam-2010-b1-partial-power-sum
        exponent index precision)
       (expt
        (putnam-2010-b1-sequence-approx
         index precision)
        exponent)))))

;; For fixed EXPONENT and TERMS, the common-precision partial sums converge to
;; the exact real partial sum. Requiring every sufficiently fine rational
;; precision to lie within EPSILON of EXPONENT therefore expresses that the
;; exact partial sum is within EPSILON, up to harmless epsilon rescaling.

(defun-sk putnam-2010-b1-partial-sum-close-below-p
    (exponent terms epsilon precision-bound)
  (forall (precision)
    (implies
     (and
      (putnam-2010-b1-positive-rational-p precision)
      (<= precision precision-bound))
     (let ((partial-sum
            (putnam-2010-b1-partial-power-sum
             exponent terms precision)))
       (and
        (rationalp partial-sum)
        (< (abs (- partial-sum exponent))
           epsilon))))))

(defun-sk putnam-2010-b1-partial-sum-close-p
    (exponent terms epsilon)
  (exists (precision-bound)
    (and
     (putnam-2010-b1-positive-rational-p precision-bound)
     (<= precision-bound epsilon)
     (putnam-2010-b1-partial-sum-close-below-p
      exponent terms epsilon precision-bound))))

(defun-sk putnam-2010-b1-series-tail-p
    (exponent epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (putnam-2010-b1-partial-sum-close-p
      exponent terms epsilon))))

(defun-sk putnam-2010-b1-series-cutoff-exists-p
    (exponent epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2010-b1-series-tail-p
      exponent epsilon cutoff))))

(defun-sk putnam-2010-b1-series-sums-to-exponent-p
    (exponent)
  (forall (epsilon)
    (implies
     (putnam-2010-b1-positive-rational-p epsilon)
     (putnam-2010-b1-series-cutoff-exists-p
      exponent epsilon))))

(defun-sk putnam-2010-b1-all-power-series-sum-p ()
  (forall (exponent)
    (implies
     (and
      (natp exponent)
      (< 0 exponent))
     (putnam-2010-b1-series-sums-to-exponent-p
      exponent))))

(defun putnambench-putnam-2010-b1-statement ()
  (implies
   (putnam-2010-b1-regular-real-sequence-name-p)
   (not
    (putnam-2010-b1-all-power-series-sum-p))))

(value-triple :itpeval-statement-checked)
:q
