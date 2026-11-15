;; Statement-only formalization of PutnamBench corpus artifact putnam_1997_a3:
;; the improper integral of the product of the specified two real power
;; series converges to sqrt(exp(1)). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defun putnam-1997-a3-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1997-a3-factorial (- n 1)))))

;; These exact rational prefixes are the two source power series. Their
;; denominators are respectively
;;
;;   product_(i<n) 2(i+1)       = 2^n n!
;;   product_(i<n) (2(i+1))^2   = (2^n n!)^2.

(defun putnam-1997-a3-series1-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- terms 1)))
      (+ (putnam-1997-a3-series1-prefix x index)
         (/ (* (expt -1 index)
               (expt x (+ (* 2 index) 1)))
            (* (expt 2 index)
               (putnam-1997-a3-factorial index)))))))

(defun putnam-1997-a3-series2-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (even-factorial
            (* (expt 2 index)
               (putnam-1997-a3-factorial index))))
      (+ (putnam-1997-a3-series2-prefix x index)
         (/ (expt x (* 2 index))
            (* even-factorial even-factorial))))))

(defun putnam-1997-a3-integrand-prefix (x terms)
  (* (putnam-1997-a3-series1-prefix x terms)
     (putnam-1997-a3-series2-prefix x terms)))

;; A midpoint sum with rational endpoint UPPER. As PARTITIONS and TERMS tend
;; to infinity, compact-uniform convergence of the two power series makes
;; this converge to the source integral on [0, UPPER].

(defun putnam-1997-a3-midpoint-sum-aux
    (upper partitions terms points)
  (declare (xargs :measure (nfix points)))
  (if (zp points)
      0
    (let* ((index (- points 1))
           (midpoint
            (/ (* upper (+ (* 2 index) 1))
               (* 2 partitions))))
      (+ (putnam-1997-a3-midpoint-sum-aux
          upper partitions terms index)
         (putnam-1997-a3-integrand-prefix
          midpoint terms)))))

(defun putnam-1997-a3-integral-prefix
    (upper partitions terms)
  (if (and (rationalp upper)
           (posp partitions)
           (natp terms))
      (* (/ upper partitions)
         (putnam-1997-a3-midpoint-sum-aux
          upper partitions terms partitions))
    0))

;; The Rocq ground truth identifies the answer as sqrt(exp(1)). Its positive
;; value is exp(1/2), represented here by exact rational Taylor prefixes.

(defun putnam-1997-a3-solution-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- terms 1)))
      (+ (putnam-1997-a3-solution-prefix index)
         (/ (expt (/ 1 2) index)
            (putnam-1997-a3-factorial index))))))

;; For a fixed rational upper endpoint, this is the simultaneous tail
;; condition for the midpoint partitions, the two source power-series
;; prefixes (which share SERIES-TERMS), and the exp(1/2) solution prefix.
;; It is not a bounded approximation: every index at or beyond CUTOFF is
;; universally quantified.  Thus this is the epsilon definition that the
;; three rational Cauchy nets have one common real limit.

(defun-sk putnam-1997-a3-approximation-tail-p
    (epsilon upper cutoff)
  (forall (partitions series-terms solution-terms)
    (implies
     (and
      (posp partitions)
      (natp cutoff)
      (<= cutoff partitions)
      (natp series-terms)
      (<= cutoff series-terms)
      (natp solution-terms)
      (<= cutoff solution-terms))
     (<
      (abs
       (- (putnam-1997-a3-integral-prefix
           upper partitions series-terms)
          (putnam-1997-a3-solution-prefix
           solution-terms)))
      epsilon))))

(defun-sk putnam-1997-a3-approximation-cutoff-exists-p
    (epsilon upper)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1997-a3-approximation-tail-p
      epsilon upper cutoff))))

;; Positive rational tolerances are cofinal in the positive reals. Rational
;; upper endpoints are cofinal at +infinity, and continuity of the integrand
;; makes their improper-integral limit equivalent to the source real-endpoint
;; limit. The quantifier order below is the nested source limit: after choosing
;; an eventual upper threshold, each later endpoint has its own eventual
;; approximation threshold.  The exp(1/2) prefix is an exact Cauchy
;; representative of sqrt(exp(1)), not a replacement by one finite prefix.

(defun-sk putnam-1997-a3-improper-tail-p
    (epsilon upper-cutoff)
  (forall (upper)
    (implies
     (and
      (rationalp upper)
      (<= upper-cutoff upper))
     (putnam-1997-a3-approximation-cutoff-exists-p
      epsilon upper))))

(defun-sk putnam-1997-a3-improper-cutoff-exists-p
    (epsilon)
  (exists (upper-cutoff)
    (and
     (rationalp upper-cutoff)
     (putnam-1997-a3-improper-tail-p
      epsilon upper-cutoff))))

(defun-sk putnambench-putnam-1997-a3-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1997-a3-improper-cutoff-exists-p
      epsilon))))

(value-triple :itpeval-statement-checked)
:q
