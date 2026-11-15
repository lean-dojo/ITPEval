;; Statement-only formalization of PutnamBench corpus artifact putnam_1982_a2:
;; convergence of the real series whose nth term uses
;; B_n(x) = sum_(k=1)^n k^x at x = log_n(2), divided by
;; (n*log_2(n))^2. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; For positive rational x, this is the finite atanh-series prefix
;;
;;   2 * sum_(j < terms) z^(2j+1)/(2j+1),  z = (x-1)/(x+1),
;;
;; which converges to the real logarithm of x.
(defun putnam-1982-a2-log-atanh-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (exponent (+ (* 2 index) 1)))
      (+ (putnam-1982-a2-log-atanh-prefix z index)
         (/ (* 2 (expt z exponent))
            exponent)))))

(defun putnam-1982-a2-log-prefix (x terms)
  (if (and (rationalp x)
           (< 0 x)
           (natp terms))
      (putnam-1982-a2-log-atanh-prefix
       (/ (- x 1) (+ x 1))
       terms)
    0))

(defun putnam-1982-a2-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1982-a2-factorial (- n 1)))))

;; This exact rational Taylor prefix converges to exp(x).
(defun putnam-1982-a2-exp-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- terms 1)))
      (+ (putnam-1982-a2-exp-prefix x index)
         (/ (expt x index)
            (putnam-1982-a2-factorial index))))))

;; The limit as PRECISION tends to infinity is
;;
;;   base^(log_n 2) = exp(log(base) * log(2) / log(n)).
(defun putnam-1982-a2-power-approx
    (base n precision)
  (if (and (natp base)
           (< 0 base)
           (natp n)
           (<= 2 n)
           (posp precision))
      (let* ((log-base
              (putnam-1982-a2-log-prefix base precision))
             (log-two
              (putnam-1982-a2-log-prefix 2 precision))
             (log-n
              (putnam-1982-a2-log-prefix n precision))
             (exponent (* log-base (/ log-two log-n))))
        (putnam-1982-a2-exp-prefix exponent precision))
    0))

(defun putnam-1982-a2-b-approx-aux
    (n remaining precision)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (putnam-1982-a2-b-approx-aux
        n (- remaining 1) precision)
       (putnam-1982-a2-power-approx
        remaining n precision))))

;; This converges to B_n(log_n 2) with exactly the source range 1 <= k <= n.
(defun putnam-1982-a2-b-approx (n precision)
  (if (and (posp n)
           (posp precision))
      (putnam-1982-a2-b-approx-aux n n precision)
    0))

;; This converges to
;;
;;   B_n(log_n 2) / (n * log_2(n))^2.
(defun putnam-1982-a2-term-approx (n precision)
  (if (and (natp n)
           (<= 2 n)
           (posp precision))
      (let* ((log-two
              (putnam-1982-a2-log-prefix 2 precision))
             (log-n
              (putnam-1982-a2-log-prefix n precision))
             (log-base-two-n (/ log-n log-two))
             (denominator
              (expt (* n log-base-two-n) 2)))
        (/ (putnam-1982-a2-b-approx n precision)
           denominator))
    0))

(defun putnam-1982-a2-series-prefix-approx
    (upper precision)
  (declare (xargs :measure (nfix upper)))
  (if (or (not (natp upper))
          (< upper 2))
      0
    (+ (putnam-1982-a2-series-prefix-approx
        (- upper 1) precision)
       (putnam-1982-a2-term-approx upper precision))))

;; For every fixed UPPER, increasing PRECISION makes the preceding exact
;; rational expression converge to the source real partial sum through UPPER.
;; This follows definitionally from the atanh series for log, the Taylor
;; series for exp, and the finite k- and n-sums above.  In particular, no
;; single diagonal choice of precision is substituted for the real sequence.
;;
;; The next predicate states that the exact real distance between two such
;; Cauchy names is strictly below EPSILON.  The positive rational MARGIN makes
;; strictness exact: the approximating distances are eventually below
;; EPSILON-MARGIN.  Both MARGIN and the unbounded precision cutoff remain
;; internal existential witnesses.
(defun-sk putnam-1982-a2-approximation-tail-p
    (left-index right-index epsilon margin precision-cutoff)
  (forall (precision)
    (implies
     (and (natp precision)
          (<= precision-cutoff precision))
     (< (abs
         (- (putnam-1982-a2-series-prefix-approx
             left-index precision)
            (putnam-1982-a2-series-prefix-approx
             right-index precision)))
        (- epsilon margin)))))

(defun-sk putnam-1982-a2-exact-distance-within-p
    (left-index right-index epsilon)
  (exists (margin precision-cutoff)
    (and (rationalp margin)
         (< 0 margin)
         (< margin epsilon)
         (posp precision-cutoff)
         (putnam-1982-a2-approximation-tail-p
          left-index
          right-index
          epsilon
          margin
          precision-cutoff))))

;; This is the Cauchy criterion for the exact real partial sums represented by
;; the full precision-indexed names, not for a selected rational diagonal.
;; Completeness of the reals and cofinality of positive rational tolerances
;; make it bidirectionally equivalent to existence of the source's real limit.
(defun-sk putnam-1982-a2-cauchy-tail-p
    (epsilon cutoff)
  (forall (left-index right-index)
    (implies
     (and (natp left-index)
          (<= cutoff left-index)
          (natp right-index)
          (<= cutoff right-index))
     (putnam-1982-a2-exact-distance-within-p
      left-index right-index epsilon))))

(defun-sk putnam-1982-a2-cauchy-cutoff-exists-p
    (epsilon)
  (exists (cutoff)
    (and (natp cutoff)
         (putnam-1982-a2-cauchy-tail-p
          epsilon cutoff))))

(defun-sk putnambench-putnam-1982-a2-statement ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (putnam-1982-a2-cauchy-cutoff-exists-p
      epsilon))))

(value-triple :itpeval-statement-checked)
:q
