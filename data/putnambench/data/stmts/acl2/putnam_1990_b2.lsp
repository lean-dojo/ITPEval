;; Statement-only formalization of PutnamBench corpus artifact putnam_1990_b2:
;; for real |x| < 1 and |z| > 1, the infinite series whose terms use the
;; specified finite-product quotients has sum -1. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative generic functions are arbitrary rational Cauchy names
;; for the source reals x, z, and P(j).  The hypotheses in the root predicate
;; explicitly require rational values and the regular Cauchy law.  Every real
;; has such a name, so this is an exact presentation of the real domain rather
;; than a restriction to rational values.

(defstub p90b2-x-approx (index) t)
(defstub p90b2-z-approx (index) t)
(defstub p90b2-p-approx (j index) t)

(defun p90b2-positive-rational-p (value)
  (and (rationalp value)
       (< 0 value)))

(defun p90b2-cauchy-radius (index)
  (/ 1 (+ 1 (nfix index))))

(defun-sk p90b2-x-rational-values-p ()
  (forall (index)
    (implies (natp index)
             (rationalp (p90b2-x-approx index)))))

(defun-sk p90b2-z-rational-values-p ()
  (forall (index)
    (implies (natp index)
             (rationalp (p90b2-z-approx index)))))

(defun-sk p90b2-p-rational-values-p ()
  (forall (j index)
    (implies (and (posp j)
                  (natp index))
             (rationalp (p90b2-p-approx j index)))))

(defun-sk p90b2-x-regular-cauchy-p ()
  (forall (left-index right-index)
    (implies
     (and (natp left-index)
          (natp right-index))
     (<=
      (abs
       (- (p90b2-x-approx left-index)
          (p90b2-x-approx right-index)))
      (+ (p90b2-cauchy-radius left-index)
         (p90b2-cauchy-radius right-index))))))

(defun-sk p90b2-z-regular-cauchy-p ()
  (forall (left-index right-index)
    (implies
     (and (natp left-index)
          (natp right-index))
     (<=
      (abs
       (- (p90b2-z-approx left-index)
          (p90b2-z-approx right-index)))
      (+ (p90b2-cauchy-radius left-index)
         (p90b2-cauchy-radius right-index))))))

(defun-sk p90b2-p-regular-cauchy-p ()
  (forall (j left-index right-index)
    (implies
     (and (posp j)
          (natp left-index)
          (natp right-index))
     (<=
      (abs
       (- (p90b2-p-approx j left-index)
          (p90b2-p-approx j right-index)))
      (+ (p90b2-cauchy-radius left-index)
         (p90b2-cauchy-radius right-index))))))

;; Strict inequalities between represented reals use an eventual rational
;; margin.  For regular Cauchy names these predicates are exactly |x| < 1 and
;; |z| > 1.

(defun-sk p90b2-x-inside-unit-tail-p (margin cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (< (abs (p90b2-x-approx index))
        (- 1 margin)))))

(defun-sk p90b2-x-inside-unit-p ()
  (exists (margin cutoff)
    (and (p90b2-positive-rational-p margin)
         (< margin 1)
         (natp cutoff)
         (p90b2-x-inside-unit-tail-p
          margin cutoff))))

(defun-sk p90b2-z-outside-unit-tail-p (margin cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (< (+ 1 margin)
        (abs (p90b2-z-approx index))))))

(defun-sk p90b2-z-outside-unit-p ()
  (exists (margin cutoff)
    (and (p90b2-positive-rational-p margin)
         (natp cutoff)
         (p90b2-z-outside-unit-tail-p
          margin cutoff))))

;; At each approximation index these are the source finite products
;;
;;   product_(i=0)^(j-1) (1-z*x^i)
;;   product_(i=1)^j     (z-x^i).
;;
;; Their quotient converges to the corresponding quotient of represented
;; reals.  The source bounds make its denominator nonzero in the real limit.

(defun p90b2-numerator-approx (j index)
  (declare (xargs :measure (nfix j)))
  (if (zp j)
      1
    (let ((i (- j 1)))
      (*
       (p90b2-numerator-approx i index)
       (- 1
          (* (p90b2-z-approx index)
             (expt (p90b2-x-approx index) i)))))))

(defun p90b2-denominator-approx (j index)
  (declare (xargs :measure (nfix j)))
  (if (zp j)
      1
    (*
     (p90b2-denominator-approx (- j 1) index)
     (- (p90b2-z-approx index)
        (expt (p90b2-x-approx index) j)))))

(defun p90b2-product-quotient-approx (j index)
  (/ (p90b2-numerator-approx j index)
     (p90b2-denominator-approx j index)))

;; Equality of two represented reals is equality of their limits.  Thus the
;; following unbounded epsilon-tail condition states P(j) equal to the exact
;; finite-product quotient for every source index j >= 1.

(defun-sk p90b2-p-formula-tail-p
    (j epsilon cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (<
      (abs
       (- (p90b2-p-approx j index)
          (p90b2-product-quotient-approx
           j index)))
      epsilon))))

(defun-sk p90b2-p-formula-cutoff-exists-p
    (j epsilon)
  (exists (cutoff)
    (and (natp cutoff)
         (p90b2-p-formula-tail-p
          j epsilon cutoff))))

(defun-sk p90b2-p-formula-at-j-p (j)
  (forall (epsilon)
    (implies
     (p90b2-positive-rational-p epsilon)
     (p90b2-p-formula-cutoff-exists-p
      j epsilon))))

(defun-sk p90b2-p-formula-p ()
  (forall (j)
    (implies (posp j)
             (p90b2-p-formula-at-j-p j))))

;; This is the rational Cauchy approximation to
;;
;;   1 + sum_(j=1)^terms (1+x^j) P(j).
;;
;; No telescoping identity or convergence rate is assumed in its definition.

(defun p90b2-partial-sum-approx (terms index)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      1
    (+
     (p90b2-partial-sum-approx
      (- terms 1) index)
     (*
      (+ 1
         (expt (p90b2-x-approx index)
               terms))
      (p90b2-p-approx terms index)))))

;; For a fixed number of terms, this predicate says that the exact represented
;; partial sum has absolute value below EPSILON.  The internal rational margin
;; is equivalent to strict real inequality and is not an approximation.

(defun-sk p90b2-partial-sum-below-tail-p
    (terms margin cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (< (abs
         (p90b2-partial-sum-approx
          terms index))
        margin))))

(defun-sk p90b2-partial-sum-below-p
    (terms epsilon)
  (exists (margin cutoff)
    (and (p90b2-positive-rational-p margin)
         (< margin epsilon)
         (natp cutoff)
         (p90b2-partial-sum-below-tail-p
          terms margin cutoff))))

;; The source infinite-sum conclusion is precisely the unbounded epsilon-N
;; assertion that these real partial sums tend to zero.

(defun-sk p90b2-series-tail-p (epsilon start)
  (forall (terms)
    (implies
     (and (natp terms)
          (<= start terms))
     (p90b2-partial-sum-below-p
      terms epsilon))))

(defun-sk p90b2-series-cutoff-exists-p (epsilon)
  (exists (start)
    (and (natp start)
         (p90b2-series-tail-p
          epsilon start))))

(defun-sk p90b2-series-converges-to-zero-p ()
  (forall (epsilon)
    (implies
     (p90b2-positive-rational-p epsilon)
     (p90b2-series-cutoff-exists-p epsilon))))

(defun putnambench-putnam-1990-b2-statement ()
  (implies
   (and
    (p90b2-x-rational-values-p)
    (p90b2-z-rational-values-p)
    (p90b2-p-rational-values-p)
    (p90b2-x-regular-cauchy-p)
    (p90b2-z-regular-cauchy-p)
    (p90b2-p-regular-cauchy-p)
    (p90b2-x-inside-unit-p)
    (p90b2-z-outside-unit-p)
    (p90b2-p-formula-p))
   (p90b2-series-converges-to-zero-p)))

(value-triple :itpeval-statement-checked)
:q
