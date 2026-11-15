;; Statement-only formalization of PutnamBench corpus artifact putnam_2017_a3:
;; strict growth and divergence of integral power ratios for distinct positive
;; continuous real functions with equal integrals. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The three DEFSTUB symbols are arbitrary regular Cauchy names, not
;; rational-valued functions or finite tables.  F-APPROX(x,e) and
;; G-APPROX(x,e), for rational x in [0,1], name the function values to error
;; at most e; I-APPROX(n,e) similarly names I_n.  Every real has such a name.
;; Conversely, the regularity inequalities below make each name converge to a
;; unique real.
;;
;; Uniformly continuous Cauchy data on the rational points of [0,1] extend
;; uniquely to continuous real functions on [0,1], and restriction gives the
;; inverse representation.  Thus the DEFSTUB symbols cover arbitrary source
;; functions.  Values outside the source interval are irrelevant, and every
;; continuous interval function has a continuous total extension.
;;
;; The positive affine substitution x=a+(b-a)t is bidirectional: from source
;; f and g define F(t)=(b-a)f(x) and G(t)=(b-a)g(x).  It preserves positivity,
;; distinctness, both base integrals, every displayed moment integral, and the
;; sequence I.  Conversely, [0,1] is a source interval.  Hence the normalized
;; statement below is equivalent in both directions to the source theorem.
;;
;; All integral predicates are unbounded double limits of right Riemann sums:
;; subdivisions tend to infinity and Cauchy-name precision tends to zero.
;; For continuous functions these limits are exactly the source integrals;
;; endpoint inclusion is immaterial.  The strict-order witnesses and rational
;; at-top bounds are also exact: regular-name error estimates give both
;; directions, and rational bounds are cofinal in the reals.
;;
;; The antecedent is non-vacuous.  Standard Cauchy names for F(t)=t+1/2,
;; G(t)=1, and I_n=integral_0^1 F(t)^(n+1) dt satisfy it: F and G are positive
;; continuous and distinct, and both base integrals equal 1.

(defstub p17a3-f-approx (x precision) t)
(defstub p17a3-g-approx (x precision) t)
(defstub p17a3-i-approx (n precision) t)

(defun p17a3-positive-rational-p (value)
  (and
   (rationalp value)
   (< 0 value)))

(defun p17a3-unit-rational-p (value)
  (and
   (rationalp value)
   (<= 0 value)
   (<= value 1)))

(defun p17a3-function-approx (which x precision)
  (if (equal which :f)
      (p17a3-f-approx x precision)
    (p17a3-g-approx x precision)))

;; Regular Cauchy names represent exact real values at every rational point.

(defun-sk p17a3-function-regular-p (which)
  (forall (x epsilon eta)
    (implies
     (and
      (p17a3-unit-rational-p x)
      (p17a3-positive-rational-p epsilon)
      (p17a3-positive-rational-p eta))
     (let ((left
            (p17a3-function-approx which x epsilon))
           (right
            (p17a3-function-approx which x eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<=
         (abs (- left right))
         (+ epsilon eta)))))))

(defun-sk p17a3-sequence-regular-p ()
  (forall (n epsilon eta)
    (implies
     (and
      (natp n)
      (p17a3-positive-rational-p epsilon)
      (p17a3-positive-rational-p eta))
     (let ((left
            (p17a3-i-approx n epsilon))
           (right
            (p17a3-i-approx n eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<=
         (abs (- left right))
         (+ epsilon eta)))))))

;; This rational epsilon-delta condition is equivalent to uniform continuity
;; of the represented function.  Compactness makes it equivalent to the
;; source's ordinary continuity on the closed interval.

(defun-sk p17a3-uniform-continuity-scale-p
    (which epsilon delta)
  (forall (x y)
    (implies
     (and
      (p17a3-unit-rational-p x)
      (p17a3-unit-rational-p y)
      (< (abs (- x y)) delta))
     (<
      (abs
       (-
        (p17a3-function-approx
         which x (* 1/8 epsilon))
        (p17a3-function-approx
         which y (* 1/8 epsilon))))
      (* 3/4 epsilon)))))

(defun-sk p17a3-uniform-continuity-radius-exists-p
    (which epsilon)
  (exists (delta)
    (and
     (p17a3-positive-rational-p delta)
     (p17a3-uniform-continuity-scale-p
      which epsilon delta))))

(defun-sk p17a3-continuous-on-unit-p (which)
  (forall (epsilon)
    (implies
     (p17a3-positive-rational-p epsilon)
     (p17a3-uniform-continuity-radius-exists-p
      which epsilon))))

;; A positive continuous function on a compact interval has a positive
;; minimum.  The following Cauchy-name lower margin is exactly that condition.

(defun-sk p17a3-positive-margin-p (which margin)
  (forall (x epsilon)
    (implies
     (and
      (p17a3-unit-rational-p x)
      (p17a3-positive-rational-p epsilon))
     (<=
      margin
      (+
       (p17a3-function-approx which x epsilon)
       epsilon)))))

(defun-sk p17a3-positive-on-unit-p (which)
  (exists (margin)
    (and
     (p17a3-positive-rational-p margin)
     (p17a3-positive-margin-p which margin))))

;; By density and continuity, two represented functions differ on [0,1] iff
;; they differ at a rational point.  A gap exceeding twice the name error is
;; equivalent to strict inequality of the corresponding exact real values.

(defun-sk p17a3-functions-distinct-on-unit-p ()
  (exists (x precision)
    (and
     (p17a3-unit-rational-p x)
     (p17a3-positive-rational-p precision)
     (<
      (* 2 precision)
      (abs
       (-
        (p17a3-f-approx x precision)
        (p17a3-g-approx x precision)))))))

;; Exact rational approximations to uniform right-endpoint Riemann sums.

(defun p17a3-function-grid-sum-aux
    (which subdivisions remaining precision)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (p17a3-function-approx
      which
      (/ remaining subdivisions)
      precision)
     (p17a3-function-grid-sum-aux
      which
      subdivisions
      (- remaining 1)
      precision))))

(defun p17a3-function-grid-sum
    (which subdivisions precision)
  (if (posp subdivisions)
      (/
       (p17a3-function-grid-sum-aux
        which subdivisions subdivisions precision)
       subdivisions)
    0))

(defun p17a3-moment-grid-sum-aux
    (n subdivisions remaining precision)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((x (/ remaining subdivisions))
           (left
            (p17a3-f-approx x precision))
           (right
            (p17a3-g-approx x precision))
           (term
            (/
             (expt left (+ n 1))
             (expt right n))))
      (+
       term
       (p17a3-moment-grid-sum-aux
        n
        subdivisions
        (- remaining 1)
        precision)))))

(defun p17a3-moment-grid-sum
    (n subdivisions precision)
  (if (and (natp n) (posp subdivisions))
      (/
       (p17a3-moment-grid-sum-aux
        n subdivisions subdivisions precision)
       subdivisions)
    0))

;; Equality of the two exact base integrals.  Both the mesh and value
;; precision quantifiers are unbounded; no finite approximation is substituted
;; for either integral.

(defun-sk p17a3-base-integral-tail-p
    (epsilon cutoff precision-bound)
  (forall (subdivisions precision)
    (implies
     (and
      (posp subdivisions)
      (<= cutoff subdivisions)
      (p17a3-positive-rational-p precision)
      (<= precision precision-bound))
     (<
      (abs
       (-
        (p17a3-function-grid-sum
         :f subdivisions precision)
        (p17a3-function-grid-sum
         :g subdivisions precision)))
      epsilon))))

(defun-sk p17a3-base-integral-cutoffs-exist-p (epsilon)
  (exists (cutoff precision-bound)
    (and
     (posp cutoff)
     (p17a3-positive-rational-p precision-bound)
     (p17a3-base-integral-tail-p
      epsilon cutoff precision-bound))))

(defun-sk p17a3-equal-base-integrals-p ()
  (forall (epsilon)
    (implies
     (p17a3-positive-rational-p epsilon)
     (p17a3-base-integral-cutoffs-exist-p epsilon))))

;; Exact equality I_n = integral F^(n+1)/G^n.  Positivity of G supplies a
;; uniform nonzero denominator below a sufficiently small precision bound.

(defun-sk p17a3-moment-value-tail-p
    (n epsilon cutoff precision-bound)
  (forall (subdivisions function-precision sequence-precision)
    (implies
     (and
      (posp subdivisions)
      (<= cutoff subdivisions)
      (p17a3-positive-rational-p function-precision)
      (<= function-precision precision-bound)
      (p17a3-positive-rational-p sequence-precision)
      (<= sequence-precision precision-bound))
     (<
      (abs
       (-
        (p17a3-moment-grid-sum
         n subdivisions function-precision)
        (p17a3-i-approx n sequence-precision)))
      epsilon))))

(defun-sk p17a3-moment-value-cutoffs-exist-p
    (n epsilon)
  (exists (cutoff precision-bound)
    (and
     (posp cutoff)
     (p17a3-positive-rational-p precision-bound)
     (p17a3-moment-value-tail-p
      n epsilon cutoff precision-bound))))

(defun-sk p17a3-moment-value-p (n)
  (forall (epsilon)
    (implies
     (p17a3-positive-rational-p epsilon)
     (p17a3-moment-value-cutoffs-exist-p
      n epsilon))))

(defun-sk p17a3-moment-sequence-definition-p ()
  (forall (n)
    (implies
     (posp n)
     (p17a3-moment-value-p n))))

;; Exact strict inequality for regular Cauchy names.

(defun-sk p17a3-strict-step-p (n)
  (exists (precision)
    (and
     (p17a3-positive-rational-p precision)
     (<
      (+
       (p17a3-i-approx n precision)
       (* 2 precision))
      (p17a3-i-approx (+ n 1) precision)))))

(defun-sk p17a3-strictly-increasing-positive-p ()
  (forall (n)
    (implies
     (posp n)
     (p17a3-strict-step-p n))))

;; Exact at-top divergence.  P17A3-I-ABOVE-BOUND-P is equivalent to the exact
;; real value I_n exceeding BOUND.  Quantifying over rational BOUND is
;; equivalent to quantifying over all real bounds by rational cofinality.

(defun-sk p17a3-i-above-bound-p (n bound)
  (exists (precision)
    (and
     (p17a3-positive-rational-p precision)
     (<
      (+ bound precision)
      (p17a3-i-approx n precision)))))

(defun-sk p17a3-above-bound-tail-p (bound cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (p17a3-i-above-bound-p n bound))))

(defun-sk p17a3-above-bound-cutoff-exists-p (bound)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p17a3-above-bound-tail-p
      bound cutoff))))

(defun-sk p17a3-tends-to-positive-infinity-p ()
  (forall (bound)
    (implies
     (rationalp bound)
     (p17a3-above-bound-cutoff-exists-p bound))))

(defun putnambench-putnam-2017-a3-statement ()
  (implies
   (and
    (p17a3-function-regular-p :f)
    (p17a3-function-regular-p :g)
    (p17a3-sequence-regular-p)
    (p17a3-continuous-on-unit-p :f)
    (p17a3-continuous-on-unit-p :g)
    (p17a3-positive-on-unit-p :f)
    (p17a3-positive-on-unit-p :g)
    (p17a3-equal-base-integrals-p)
    (p17a3-functions-distinct-on-unit-p)
    (p17a3-moment-sequence-definition-p))
   (and
    (p17a3-strictly-increasing-positive-p)
    (p17a3-tends-to-positive-infinity-p))))

(value-triple :itpeval-statement-checked)
:q
