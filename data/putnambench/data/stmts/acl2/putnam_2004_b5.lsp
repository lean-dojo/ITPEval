;; Statement-only formalization of PutnamBench corpus artifact putnam_2004_b5:
;; the left limit at 1 of the stated infinite product is 2 / exp(1).
;; This file contains no proof.
;;
;; For 0 < x < 1, taking logarithms and summing by parts rewrites the
;; logarithm of the first N factors as
;;
;;   -log 2
;;   + (1-x) * sum_{m=1}^{N-1} x^(m-1) log(1+x^m)
;;   + x^(N-1) log(1+x^N).
;;
;; The middle term is a geometric Riemann sum for
;; integral_0^1 log(1+t) dt = 2 log 2 - 1.  Thus the product limit has
;; logarithm log 2 - 1, equivalently the product is 2 / exp(1).
;; PUTNAM-2004-B5-LOG-APPROX is the standard rational atanh series for
;; log. Rational epsilon and x form cofinal and dense presentations of the
;; corresponding real conditions.
;; The product hypothesis uniquely determines xprod on 0 < x < 1, so
;; eliminating that auxiliary function is bidirectionally equivalent to
;; the source statement; the inclusive Isabelle indexing differs only by
;; one term and has the same infinite product.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defun putnam-2004-b5-log-series-aux (u power odd remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (/ power odd)
       (putnam-2004-b5-log-series-aux
        u
        (* power u u)
        (+ odd 2)
        (- remaining 1)))))

(defun putnam-2004-b5-log-approx (base terms)
  (if (and (rationalp base)
           (< 0 base)
           (natp terms))
      (let ((u (/ (- base 1) (+ base 1))))
        (* 2
           (putnam-2004-b5-log-series-aux u u 1 terms)))
    0))

(defun putnam-2004-b5-weighted-log-prefix (x upper log-terms)
  (declare (xargs :measure (nfix upper)))
  (if (zp upper)
      0
    (+ (putnam-2004-b5-weighted-log-prefix
        x (- upper 1) log-terms)
       (* (expt x (- upper 1))
          (putnam-2004-b5-log-approx
           (+ 1 (expt x upper))
           log-terms)))))

(defun putnam-2004-b5-log-product-approx (x terms log-terms)
  (if (and (rationalp x)
           (< 0 x)
           (< x 1)
           (posp terms)
           (natp log-terms))
      (+ (- (putnam-2004-b5-log-approx 2 log-terms))
         (* (- 1 x)
            (putnam-2004-b5-weighted-log-prefix
             x (- terms 1) log-terms))
         (* (expt x (- terms 1))
            (putnam-2004-b5-log-approx
             (+ 1 (expt x terms))
             log-terms)))
    0))

(defun putnam-2004-b5-log-solution-approx (log-terms)
  (- (putnam-2004-b5-log-approx 2 log-terms) 1))

;; The source gives no convergence rates. The quantifiers below state the
;; left-limit definition directly: every tolerance has a left neighborhood,
;; and at every rational point in that neighborhood the finite-product and
;; logarithm approximations eventually remain within the tolerance.

(defun-sk putnam-2004-b5-approximation-tail-p
    (epsilon x product-cutoff log-cutoff)
  (forall (terms log-terms)
    (implies
     (and
      (natp terms)
      (<= product-cutoff terms)
      (natp log-terms)
      (<= log-cutoff log-terms))
     (< (abs
         (- (putnam-2004-b5-log-product-approx
             x terms log-terms)
            (putnam-2004-b5-log-solution-approx
             log-terms)))
        epsilon))))

(defun-sk putnam-2004-b5-approximation-cutoffs-exist-p
    (epsilon x)
  (exists (product-cutoff log-cutoff)
    (and
     (posp product-cutoff)
     (posp log-cutoff)
     (putnam-2004-b5-approximation-tail-p
      epsilon x product-cutoff log-cutoff))))

(defun-sk putnam-2004-b5-left-neighborhood-p
    (epsilon delta)
  (forall (x)
    (implies
     (and
      (rationalp x)
      (< 0 x)
      (< x 1)
      (< (- 1 x) delta))
     (putnam-2004-b5-approximation-cutoffs-exist-p
      epsilon x))))

(defun-sk putnam-2004-b5-delta-exists-p (epsilon)
  (exists (delta)
    (and
     (rationalp delta)
     (< 0 delta)
     (putnam-2004-b5-left-neighborhood-p
      epsilon delta))))

(defun-sk putnambench-putnam-2004-b5-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-2004-b5-delta-exists-p epsilon))))

(value-triple :itpeval-statement-checked)

:q
