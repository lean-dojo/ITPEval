;; Statement-only formalization of PutnamBench corpus artifact putnam_1972_a6:
;; vanishing lower moments and a normalized nth moment force an integrable
;; real function on [0,1] to be at least 2^n(n+1) in absolute value on a set of
;; positive Lebesgue measure. This file contains no proof.

(in-package "ACL2")

;; The universal source statement is encoded by the absence of its
;; counterexamples. A code (POINTS, VALUES) denotes the rational step function
;; with value VALUES[j] on the interval from POINTS[j] to POINTS[j+1].
;; The list can have arbitrary finite length, and the moment formula below is
;; the exact integral of that step function, not a finite sampling.
;;
;; This restriction to rational step-function counterexamples is
;; bidirectionally exact. Any encoded counterexample is directly an integrable
;; real source counterexample. Conversely, suppose a source counterexample f
;; exists and put M = 2^n(n+1). Then |f| < M almost everywhere. On the
;; finite-dimensional space of real polynomials of degree at most n, the
;; moment functional p |-> integral(p*f) is therefore strictly bounded by
;; M times the L1 norm. Compactness of the polynomial unit sphere gives a
;; uniform bound c < M. L1-L-infinity duality supplies a representative with
;; essential bound c. Rational step functions are dense in L1, and corrections
;; on n+1 small rational intervals have an invertible rational moment matrix.
;; Thus one can approximate the representative and correct all n+1 moments
;; exactly while retaining a strict bound below M. This produces an encoded
;; counterexample. Hence the predicate below has exactly the source theorem's
;; counterexamples and does not replace an arbitrary function by samples.

(defun putnam-1972-a6-rational-list-p (values)
  (if (consp values)
      (and (rationalp (car values))
           (putnam-1972-a6-rational-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1972-a6-strictly-increasing-p (points)
  (if (consp (cdr points))
      (and (< (car points) (cadr points))
           (putnam-1972-a6-strictly-increasing-p (cdr points)))
    t))

(defun putnam-1972-a6-last (values)
  (if (consp (cdr values))
      (putnam-1972-a6-last (cdr values))
    (car values)))

(defun putnam-1972-a6-step-code-p (points values)
  (and
   (true-listp points)
   (true-listp values)
   (consp values)
   (equal (len points) (+ 1 (len values)))
   (putnam-1972-a6-rational-list-p points)
   (putnam-1972-a6-rational-list-p values)
   (equal (car points) 0)
   (equal (putnam-1972-a6-last points) 1)
   (putnam-1972-a6-strictly-increasing-p points)))

;; Integral of x^POWER times the coded step function over [0,1].
(defun putnam-1972-a6-moment (power points values)
  (if (consp values)
      (+
       (*
        (car values)
        (/
         (- (expt (cadr points) (+ power 1))
            (expt (car points) (+ power 1)))
         (+ power 1)))
       (putnam-1972-a6-moment
        power (cdr points) (cdr values)))
    0))

(defun putnam-1972-a6-lower-moments-zero-p
    (remaining points values)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (equal
      (putnam-1972-a6-moment
       (- remaining 1) points values)
      0)
     (putnam-1972-a6-lower-moments-zero-p
      (- remaining 1) points values))))

(defun putnam-1972-a6-values-below-p (values bound)
  (if (consp values)
      (and (< (abs (car values)) bound)
           (putnam-1972-a6-values-below-p (cdr values) bound))
    (equal values nil)))

(defun putnam-1972-a6-threshold (n)
  (* (expt 2 n) (+ n 1)))

(defun putnam-1972-a6-step-counterexample-p
    (n points values)
  (and
   (natp n)
   (putnam-1972-a6-step-code-p points values)
   (putnam-1972-a6-lower-moments-zero-p n points values)
   (equal (putnam-1972-a6-moment n points values) 1)
   (putnam-1972-a6-values-below-p
    values
    (putnam-1972-a6-threshold n))))

(defun putnambench-putnam-1972-a6-statement
    (n points values)
  (not
   (putnam-1972-a6-step-counterexample-p
    n points values)))

(value-triple :itpeval-statement-checked)
:q
