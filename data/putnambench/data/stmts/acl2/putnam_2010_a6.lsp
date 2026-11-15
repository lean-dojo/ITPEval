;; Statement-only formalization of PutnamBench corpus artifact putnam_2010_a6:
;; a strictly decreasing continuous real function tending to zero has a
;; divergent improper integral of (f(x)-f(x+1))/f(x). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; For nonnegative rational X and positive rational EPSILON, F-APPROX is an
;; EPSILON-approximation to f(X). The regular-name and compact-continuity
;; predicates below present exactly the restriction to [0,infinity) of a
;; continuous real function. Since the source statement never uses f at a
;; negative argument, this loses no data relevant to the proposition.
(defstub putnam-2010-a6-f-approx (x epsilon) t)

(defun putnam-2010-a6-positive-rational-p (x)
  (and (rationalp x) (< 0 x)))

(defun putnam-2010-a6-nonnegative-rational-p (x)
  (and (rationalp x) (<= 0 x)))

(defun-sk putnam-2010-a6-regular-name-p ()
  (forall (x epsilon eta)
    (implies
     (and
      (putnam-2010-a6-nonnegative-rational-p x)
      (putnam-2010-a6-positive-rational-p epsilon)
      (putnam-2010-a6-positive-rational-p eta))
     (and
      (rationalp (putnam-2010-a6-f-approx x epsilon))
      (rationalp (putnam-2010-a6-f-approx x eta))
      (<=
       (abs
        (-
         (putnam-2010-a6-f-approx x epsilon)
         (putnam-2010-a6-f-approx x eta)))
       (+ epsilon eta))))))

(defun-sk putnam-2010-a6-continuity-tail-p
    (bound epsilon delta)
  (forall (x y)
    (implies
     (and
      (putnam-2010-a6-nonnegative-rational-p x)
      (putnam-2010-a6-nonnegative-rational-p y)
      (<= x bound)
      (<= y bound)
      (< (abs (- x y)) delta))
     (<=
      (abs
       (-
        (putnam-2010-a6-f-approx x (/ epsilon 8))
        (putnam-2010-a6-f-approx y (/ epsilon 8))))
      (/ epsilon 2)))))

(defun-sk putnam-2010-a6-continuity-delta-exists-p
    (bound epsilon)
  (exists (delta)
    (and
     (putnam-2010-a6-positive-rational-p delta)
     (putnam-2010-a6-continuity-tail-p
      bound epsilon delta))))

(defun-sk putnam-2010-a6-continuous-on-nonnegative-reals-p ()
  (forall (bound epsilon)
    (implies
     (and
      (posp bound)
      (putnam-2010-a6-positive-rational-p epsilon))
     (putnam-2010-a6-continuity-delta-exists-p
      bound epsilon))))

;; A positive rational gap between sufficiently accurate names is equivalent
;; to strict inequality between the represented real values.
(defun putnam-2010-a6-decrease-gap-p (x y gap)
  (and
   (putnam-2010-a6-positive-rational-p gap)
   (<=
    gap
    (-
     (putnam-2010-a6-f-approx x (/ gap 8))
     (putnam-2010-a6-f-approx y (/ gap 8))))))

(defun-sk putnam-2010-a6-decrease-gap-exists-p (x y)
  (exists (gap)
    (putnam-2010-a6-decrease-gap-p x y gap)))

(defun-sk putnam-2010-a6-strictly-decreasing-p ()
  (forall (x y)
    (implies
     (and
      (putnam-2010-a6-nonnegative-rational-p x)
      (putnam-2010-a6-nonnegative-rational-p y)
      (< x y))
     (putnam-2010-a6-decrease-gap-exists-p x y))))

(defun-sk putnam-2010-a6-zero-limit-tail-p
    (epsilon cutoff)
  (forall (x)
    (implies
     (and
      (putnam-2010-a6-nonnegative-rational-p x)
      (<= cutoff x))
     (<=
      (abs
       (putnam-2010-a6-f-approx x (/ epsilon 4)))
      (/ epsilon 2)))))

(defun-sk putnam-2010-a6-zero-limit-cutoff-exists-p
    (epsilon)
  (exists (cutoff)
    (and
     (putnam-2010-a6-nonnegative-rational-p cutoff)
     (putnam-2010-a6-zero-limit-tail-p
      epsilon cutoff))))

(defun-sk putnam-2010-a6-tends-to-zero-p ()
  (forall (epsilon)
    (implies
     (putnam-2010-a6-positive-rational-p epsilon)
     (putnam-2010-a6-zero-limit-cutoff-exists-p
      epsilon))))

;; Right Riemann sums for the continuous integrand
;; (f(x)-f(x+1))/f(x) on [0,UPPER]. DELTA is the accuracy used for each
;; regular-Cauchy name. Strict decrease together with the zero limit makes
;; f positive on [0,infinity), so the represented denominator is nonzero in
;; the limit. These sums therefore converge to the source interval integral.
(defun putnam-2010-a6-riemann-sum-aux
    (upper n i delta)
  (declare (xargs :measure (nfix i)))
  (if (zp i)
      0
    (let* ((x (* upper (/ i n)))
           (fx
            (putnam-2010-a6-f-approx x delta))
           (fx1
            (putnam-2010-a6-f-approx (+ x 1) delta))
           (integrand (/ (- fx fx1) fx)))
      (+
       (putnam-2010-a6-riemann-sum-aux
        upper n (- i 1) delta)
       (* (/ upper n) integrand)))))

(defun putnam-2010-a6-riemann-sum
    (upper n delta)
  (if
   (and
    (putnam-2010-a6-nonnegative-rational-p upper)
    (posp n)
    (putnam-2010-a6-positive-rational-p delta))
   (putnam-2010-a6-riemann-sum-aux
    upper n n delta)
   0))

;; For fixed rational endpoints X and Y, this is the exact assertion that the
;; two represented integral values differ by less than EPSILON: all
;; sufficiently fine partitions and sufficiently accurate f-values satisfy
;; the displayed bound. The four approximation thresholds are existential
;; after X and Y, so no uniform convergence rate on an unbounded interval is
;; imposed.
(defun-sk putnam-2010-a6-integral-comparison-tail-p
    (epsilon x y nx ny precision-x precision-y)
  (forall (n m delta eta)
    (implies
     (and
      (posp n)
      (posp m)
      (<= nx n)
      (<= ny m)
      (putnam-2010-a6-positive-rational-p delta)
      (putnam-2010-a6-positive-rational-p eta)
      (<= delta precision-x)
      (<= eta precision-y))
     (<
      (abs
       (-
        (putnam-2010-a6-riemann-sum x n delta)
        (putnam-2010-a6-riemann-sum y m eta)))
      epsilon))))

(defun putnam-2010-a6-integral-comparison-witness-p
    (epsilon x y witness)
  (let
      ((nx (nth 0 witness))
       (ny (nth 1 witness))
       (precision-x (nth 2 witness))
       (precision-y (nth 3 witness)))
    (and
     (true-listp witness)
     (equal (len witness) 4)
     (posp nx)
     (posp ny)
     (putnam-2010-a6-positive-rational-p precision-x)
     (putnam-2010-a6-positive-rational-p precision-y)
     (putnam-2010-a6-integral-comparison-tail-p
      epsilon x y nx ny precision-x precision-y))))

(defun-sk putnam-2010-a6-integral-comparison-exists-p
    (epsilon x y)
  (exists (witness)
    (putnam-2010-a6-integral-comparison-witness-p
     epsilon x y witness)))

(defun-sk putnam-2010-a6-integral-limit-tail-p
    (epsilon cutoff)
  (forall (x y)
    (implies
     (and
      (putnam-2010-a6-nonnegative-rational-p x)
      (putnam-2010-a6-nonnegative-rational-p y)
      (<= cutoff x)
      (<= cutoff y))
     (putnam-2010-a6-integral-comparison-exists-p
      epsilon x y))))

(defun-sk putnam-2010-a6-integral-limit-cutoff-exists-p
    (epsilon)
  (exists (cutoff)
    (and
     (putnam-2010-a6-nonnegative-rational-p cutoff)
     (putnam-2010-a6-integral-limit-tail-p
      epsilon cutoff))))

;; Completeness of the real numbers makes this Cauchy-at-infinity condition
;; equivalent to the existence of the finite real limit quantified in the
;; Lean, Isabelle, and Rocq statements. Nonnegative rationals are cofinal in
;; the real atTop filter, and continuity of the finite integral makes checking
;; them equivalent to checking all real upper endpoints.
(defun-sk putnam-2010-a6-integral-has-finite-limit-p ()
  (forall (epsilon)
    (implies
     (putnam-2010-a6-positive-rational-p epsilon)
     (putnam-2010-a6-integral-limit-cutoff-exists-p
      epsilon))))

(defun putnambench-putnam-2010-a6-statement ()
  (implies
   (and
    (putnam-2010-a6-regular-name-p)
    (putnam-2010-a6-continuous-on-nonnegative-reals-p)
    (putnam-2010-a6-strictly-decreasing-p)
    (putnam-2010-a6-tends-to-zero-p))
   (not
    (putnam-2010-a6-integral-has-finite-limit-p))))

(value-triple :itpeval-statement-checked)
:q
