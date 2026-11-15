;; Statement-only formalization of PutnamBench corpus artifact putnam_2020_a3:
;; the series of squares of the sequence a_0 = pi/2 and
;; a_(n+1) = sin(a_n) diverges. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Every real quantity used below has a concrete rational Cauchy name.  There
;; is no external carrier or interpretation premise.  A name requested at a
;; positive rational tolerance EPSILON returns a rational within EPSILON of
;; the represented standard real.

(defun p20a3-positive-rational-p (x)
  (and (rationalp x)
       (< 0 x)))

(defun p20a3-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (p20a3-factorial (- n 1)))))

;; Exact rational Taylor prefixes for arctan(z).
(defun p20a3-arctan-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (+ (* 2 index) 1))
           (sign (if (evenp index) 1 -1)))
      (+ (p20a3-arctan-prefix z index)
         (/ (* sign (expt z degree))
            degree)))))

;; Machin's identity fixes the standard constant
;;   pi = 16 arctan(1/5) - 4 arctan(1/239).
(defun p20a3-pi-prefix (terms)
  (- (* 16 (p20a3-arctan-prefix 1/5 terms))
     (* 4 (p20a3-arctan-prefix 1/239 terms))))

;; The alternating-series error is less than 20/TERMS.  Taking strictly more
;; than 20/EPSILON terms therefore gives a rational EPSILON-approximation to
;; the standard real pi.  The term count is unbounded as EPSILON tends to zero.
(defun p20a3-pi-name-value (epsilon)
  (if (p20a3-positive-rational-p epsilon)
      (p20a3-pi-prefix
       (+ 1 (floor 20 epsilon)))
    0))

;; Exact rational Maclaurin prefixes for sine.
(defun p20a3-sine-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (+ (* 2 index) 1))
           (sign (if (evenp index) 1 -1)))
      (+ (p20a3-sine-prefix x index)
         (/ (* sign (expt x degree))
            (p20a3-factorial degree))))))

;; Let A=floor(|x|)+1, D=floor(1/EPSILON)+1, and K=A^2*D.  Then A>|x|,
;; D>1/EPSILON, and the Taylor remainder after K sine terms is bounded by
;;
;;   |x|^(2K)/(2K)! < A^(2K)/K^K = (1/D)^K <= 1/D < EPSILON.
;;
;; Hence this is an exact unbounded rational Cauchy approximation to sin(x),
;; for every rational x and every requested positive rational tolerance.
(defun p20a3-sine-term-count (x epsilon)
  (if (and (rationalp x)
           (p20a3-positive-rational-p epsilon))
      (let* ((a (+ 1 (floor (abs x) 1)))
             (d (+ 1 (floor 1 epsilon))))
        (* a a d))
    1))

(defun p20a3-sine-rational-name-value (x epsilon)
  (if (and (rationalp x)
           (p20a3-positive-rational-p epsilon))
      (p20a3-sine-prefix
       x
       (p20a3-sine-term-count x epsilon))
    0))

;; This recursively names the unique source sequence.  At index zero, a
;; 2*EPSILON approximation to pi becomes an EPSILON approximation to pi/2.
;; At a successor, the previous name and the rational sine prefix each receive
;; half the error budget.  Since real sine is 1-Lipschitz, the result is within
;; EPSILON of sin(a_n).  Both the index and every precision remain unbounded.
(defun p20a3-sequence-name-value (n epsilon)
  (declare (xargs :measure (nfix n)))
  (if (not (p20a3-positive-rational-p epsilon))
      0
    (if (zp n)
        (/ (p20a3-pi-name-value (* 2 epsilon))
           2)
      (let* ((inner (/ epsilon 2))
             (previous
              (p20a3-sequence-name-value
               (- n 1)
               inner)))
        (p20a3-sine-rational-name-value
         previous
         inner)))))

;; The source partial sum at M is sum_{n=1}^M a_n^2.  Its exact rational name
;; uses one common approximation tolerance for its M sequence terms.
(defun p20a3-square-prefix-at-precision (m precision)
  (declare (xargs :measure (nfix m)))
  (if (zp m)
      0
    (let ((term
           (p20a3-sequence-name-value
            m
            precision)))
      (+ (p20a3-square-prefix-at-precision
          (- m 1)
          precision)
         (* term term)))))

;; The true iterates lie in [0,2].  With DELTA <= 1/2, their rational names
;; have absolute value below 5/2, so replacing one square changes it by less
;; than (9/2)*DELTA.  Choosing
;;
;;   DELTA <= EPSILON/(10*M)
;;
;; keeps the accumulated error in M squares below EPSILON.  Thus the function
;; below is a concrete rational Cauchy name for every finite partial sum, with
;; no finite cap on M or on the requested precision.
(defun p20a3-square-prefix-working-precision (m epsilon)
  (if (and (posp m)
           (p20a3-positive-rational-p epsilon))
      (let ((scaled (/ epsilon (* 10 m))))
        (if (< scaled 1/2)
            scaled
          1/2))
    1/2))

(defun p20a3-square-prefix-name-value (m epsilon)
  (if (and (natp m)
           (p20a3-positive-rational-p epsilon))
      (if (zp m)
          0
        (p20a3-square-prefix-at-precision
         m
         (p20a3-square-prefix-working-precision
          m
          epsilon)))
    0))

;; For an exact real partial sum S_m and its rational name q_m(epsilon),
;;
;;   q_m(epsilon) > bound + epsilon
;;
;; implies S_m > bound.  Conversely, whenever S_m > bound, some positive
;; rational epsilon smaller than half the gap makes the displayed inequality
;; true.  The precision and prefix witnesses are internal, so this predicate
;; is bidirectionally equivalent to an exact partial sum exceeding BOUND.
(defun-sk p20a3-partial-sum-above-bound-p (bound)
  (exists (m epsilon)
    (and (natp m)
         (p20a3-positive-rational-p epsilon)
         (< (+ bound epsilon)
            (p20a3-square-prefix-name-value
             m
             epsilon)))))

;; The nonnegative partial sums converge exactly when they are bounded above.
;; Rational bounds are cofinal in the reals.  Therefore universal failure of
;; rational upper bounds is equivalent, over the complete real numbers, to
;; divergence of the source series.  This is the published series statement;
;; the Rocq individual-term limit is a secondary transcription defect.
(defun-sk putnambench-putnam-2020-a3-statement ()
  (forall (bound)
    (implies (rationalp bound)
             (p20a3-partial-sum-above-bound-p
              bound))))

(value-triple :itpeval-statement-checked)

:q
