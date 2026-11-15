;; Statement-only formalization of PutnamBench corpus artifact putnam_2008_a4:
;; divergence of the reciprocal series for the real function defined by
;; f(x)=x up to e and f(x)=x*f(log x) above e. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source recurrence has a unique solution: for x>e, 1<log(x)<x, so
;; repeated logarithms reach the base branch and f(x) is the finite product
;; of that logarithmic chain.  The definitions below give rational
;; approximations to exactly that product.  A finite Taylor prefix tends to e,
;; and the atanh series
;;
;;   log(x) = 2 * sum_(j>=0) z^(2j+1)/(2j+1), z=(x-1)/(x+1),
;;
;; tends to log(x) for every positive x.  At the equality boundary, taking
;; one additional recurrence step has the same value because e*f(1)=e, so the
;; precision-dependent comparison does not change the represented real.
;;
;; For partial sums through U, the diagonal precision grows without bound
;; rapidly enough that all finitely many iterated-log and reciprocal errors
;; together tend to zero.  Hence the rational diagonal sequence is Cauchy iff
;; the source's real partial-sum sequence is Cauchy.  Completeness of the
;; reals then makes its negated Cauchy criterion equivalent to the asserted
;; nonexistence of a real limit.  Positive rational tolerances are cofinal
;; among positive real tolerances.

(defun putnam-2008-a4-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-2008-a4-factorial (- n 1)))))

(defun putnam-2008-a4-exp-one-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- terms 1)))
      (+ (putnam-2008-a4-exp-one-prefix index)
         (/ 1
            (putnam-2008-a4-factorial index))))))

(defun putnam-2008-a4-log-atanh-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (exponent (+ (* 2 index) 1)))
      (+ (putnam-2008-a4-log-atanh-prefix z index)
         (/ (* 2 (expt z exponent))
            exponent)))))

(defun putnam-2008-a4-log-prefix (x terms)
  (if (and (rationalp x)
           (< 0 x)
           (natp terms))
      (putnam-2008-a4-log-atanh-prefix
       (/ (- x 1) (+ x 1))
       terms)
    0))

;; FUEL is only a totality bound.  For the exact recurrence started at a
;; positive integer n, fewer than n+1 logarithmic steps can be taken above e.
(defun putnam-2008-a4-f-approx-aux
    (current precision fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond
   ((or (zp fuel)
        (not (rationalp current))
        (<= current 0))
    current)
   ((< (putnam-2008-a4-exp-one-prefix precision)
       current)
    (* current
       (putnam-2008-a4-f-approx-aux
        (putnam-2008-a4-log-prefix current precision)
        precision
        (- fuel 1))))
   (t current)))

(defun putnam-2008-a4-f-approx (n precision)
  (if (and (posp n)
           (posp precision))
      (putnam-2008-a4-f-approx-aux
       n precision (+ n 1))
    0))

(defun putnam-2008-a4-term-approx (n precision)
  (if (and (posp n)
           (posp precision))
      (/ 1
         (putnam-2008-a4-f-approx n precision))
    0))

(defun putnam-2008-a4-series-prefix-approx
    (upper precision)
  (declare (xargs :measure (nfix upper)))
  (if (zp upper)
      0
    (+ (putnam-2008-a4-series-prefix-approx
        (- upper 1) precision)
       (putnam-2008-a4-term-approx
        upper precision))))

(defun putnam-2008-a4-diagonal-precision (upper)
  (expt
   2
   (+ 64
      (* 64
         (expt (+ (nfix upper) 2) 3)))))

(defun putnam-2008-a4-partial-sum-approx (upper)
  (if (natp upper)
      (putnam-2008-a4-series-prefix-approx
       upper
       (putnam-2008-a4-diagonal-precision upper))
    0))

(defun-sk putnam-2008-a4-cauchy-tail-p
    (epsilon cutoff)
  (forall (left-index right-index)
    (implies
     (and (natp left-index)
          (<= cutoff left-index)
          (natp right-index)
          (<= cutoff right-index))
     (< (abs
         (- (putnam-2008-a4-partial-sum-approx
             left-index)
            (putnam-2008-a4-partial-sum-approx
             right-index)))
        epsilon))))

(defun-sk putnam-2008-a4-cauchy-cutoff-exists-p
    (epsilon)
  (exists (cutoff)
    (and (natp cutoff)
         (putnam-2008-a4-cauchy-tail-p
          epsilon cutoff))))

(defun-sk putnam-2008-a4-series-cauchy-p ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (putnam-2008-a4-cauchy-cutoff-exists-p
      epsilon))))

(defun putnambench-putnam-2008-a4-statement ()
  (not (putnam-2008-a4-series-cauchy-p)))

(value-triple :itpeval-statement-checked)
:q
