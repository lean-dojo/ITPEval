;; Statement-only formalization of PutnamBench corpus artifact putnam_2014_a4:
;; the smallest possible probability that a nonnegative integer-valued random
;; variable with first three moments 1, 2, and 5 equals zero is 1/3.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A value MASS-APPROX(INDEX, PRECISION) is a rational approximation, within
;; PRECISION, to the real probability mass at INDEX.  The regularity predicate
;; below is the standard regular-Cauchy-name presentation of a real number.
;; Thus rational approximants represent arbitrary real masses, not a
;; rational-valued or finite-support restriction.

(defstub putnam-2014-a4-arbitrary-mass-approx
  (index precision)
  t)

;; The explicit optimizer has masses 1/3, 1/2, and 1/6 at 0, 1, and 3.

(defun putnam-2014-a4-witness-mass-approx (index precision)
  (declare (ignore precision))
  (cond
   ((equal index 0) 1/3)
   ((equal index 1) 1/2)
   ((equal index 3) 1/6)
   (t 0)))

(defun putnam-2014-a4-mass-approx (distribution index precision)
  (if (equal distribution :arbitrary)
      (putnam-2014-a4-arbitrary-mass-approx index precision)
    (putnam-2014-a4-witness-mass-approx index precision)))

(defun putnam-2014-a4-positive-rational-p (value)
  (and
   (rationalp value)
   (< 0 value)))

(defun-sk putnam-2014-a4-regular-real-sequence-name-p
    (distribution)
  (forall (index epsilon eta)
    (implies
     (and
      (natp index)
      (putnam-2014-a4-positive-rational-p epsilon)
      (putnam-2014-a4-positive-rational-p eta))
     (let ((left
            (putnam-2014-a4-mass-approx
             distribution index epsilon))
           (right
            (putnam-2014-a4-mass-approx
             distribution index eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

;; For a regular Cauchy name, these approximation inequalities are
;; bidirectionally equivalent to the represented real lying in [0,1].

(defun-sk putnam-2014-a4-mass-in-unit-interval-p
    (distribution index)
  (forall (epsilon)
    (implies
     (putnam-2014-a4-positive-rational-p epsilon)
     (let ((approximation
            (putnam-2014-a4-mass-approx
             distribution index epsilon)))
       (and
        (rationalp approximation)
        (<= (- epsilon) approximation)
        (<= approximation (+ 1 epsilon)))))))

(defun-sk putnam-2014-a4-all-masses-in-unit-interval-p
    (distribution)
  (forall (index)
    (implies
     (natp index)
     (putnam-2014-a4-mass-in-unit-interval-p
      distribution index))))

;; This is a rational approximation to
;;   sum_{INDEX < TERMS} INDEX^EXPONENT * probability(INDEX).
;; Taking EXPONENT = 0 gives total probability.

(defun putnam-2014-a4-partial-moment-sum
    (distribution exponent terms precision)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- (nfix terms) 1)))
      (+
       (putnam-2014-a4-partial-moment-sum
        distribution exponent index precision)
       (*
        (expt index exponent)
        (putnam-2014-a4-mass-approx
         distribution index precision))))))

;; For fixed TERMS, sufficiently precise rational approximations determine
;; the exact real finite partial sum.  Positive rational tolerances are
;; cofinal in the positive reals, so the following tail definition is
;; equivalent to convergence of the infinite moment series to TARGET.

(defun-sk putnam-2014-a4-partial-moment-close-below-p
    (distribution exponent terms target epsilon precision-bound)
  (forall (precision)
    (implies
     (and
      (putnam-2014-a4-positive-rational-p precision)
      (<= precision precision-bound))
     (let ((partial-sum
            (putnam-2014-a4-partial-moment-sum
             distribution exponent terms precision)))
       (and
        (rationalp partial-sum)
        (< (abs (- partial-sum target))
           epsilon))))))

(defun-sk putnam-2014-a4-partial-moment-close-p
    (distribution exponent terms target epsilon)
  (exists (precision-bound)
    (and
     (putnam-2014-a4-positive-rational-p precision-bound)
     (<= precision-bound epsilon)
     (putnam-2014-a4-partial-moment-close-below-p
      distribution exponent terms target epsilon
      precision-bound))))

(defun-sk putnam-2014-a4-moment-tail-p
    (distribution exponent target epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (putnam-2014-a4-partial-moment-close-p
      distribution exponent terms target epsilon))))

(defun-sk putnam-2014-a4-moment-cutoff-exists-p
    (distribution exponent target epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2014-a4-moment-tail-p
      distribution exponent target epsilon cutoff))))

(defun-sk putnam-2014-a4-moment-sums-to-p
    (distribution exponent target)
  (forall (epsilon)
    (implies
     (putnam-2014-a4-positive-rational-p epsilon)
     (putnam-2014-a4-moment-cutoff-exists-p
      distribution exponent target epsilon))))

(defun putnam-2014-a4-distribution-p (distribution)
  (and
   (putnam-2014-a4-regular-real-sequence-name-p distribution)
   (putnam-2014-a4-all-masses-in-unit-interval-p distribution)
   (putnam-2014-a4-moment-sums-to-p distribution 0 1)
   (putnam-2014-a4-moment-sums-to-p distribution 1 1)
   (putnam-2014-a4-moment-sums-to-p distribution 2 2)
   (putnam-2014-a4-moment-sums-to-p distribution 3 5)))

;; These predicates are the exact real comparisons encoded through a regular
;; Cauchy name.

(defun-sk putnam-2014-a4-mass-at-least-rational-p
    (distribution index lower-bound)
  (forall (epsilon)
    (implies
     (putnam-2014-a4-positive-rational-p epsilon)
     (<= (- lower-bound epsilon)
         (putnam-2014-a4-mass-approx
          distribution index epsilon)))))

(defun-sk putnam-2014-a4-mass-equals-rational-p
    (distribution index target)
  (forall (epsilon)
    (implies
     (putnam-2014-a4-positive-rational-p epsilon)
     (<=
      (abs
       (-
        (putnam-2014-a4-mass-approx
         distribution index epsilon)
        target))
      epsilon))))

;; The DEFSTUB sequence is arbitrary, so the implication is the universal
;; lower bound over every admissible probability mass function.  The second
;; conjunct supplies attainability by the explicit distribution above.

(defun putnambench-putnam-2014-a4-statement ()
  (and
   (implies
    (putnam-2014-a4-distribution-p :arbitrary)
    (putnam-2014-a4-mass-at-least-rational-p
     :arbitrary 0 1/3))
   (putnam-2014-a4-distribution-p :witness)
   (putnam-2014-a4-mass-equals-rational-p
    :witness 0 1/3)))

(value-triple :itpeval-statement-checked)
:q
