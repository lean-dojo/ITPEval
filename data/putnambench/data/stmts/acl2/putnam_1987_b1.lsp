;; Statement-only formalization of PutnamBench corpus artifact putnam_1987_b1:
;; the real interval integral from 2 to 4 of the quotient formed from the
;; square roots of log(9-x) and log(x+3) equals 1. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Ordinary ACL2 has exact rational arithmetic but no primitive real numbers.
;; The definitions below therefore give the source integrand a concrete exact
;; Cauchy-real presentation, with no abstract carrier or uninterpreted real
;; operation.
;;
;; For 1 < Y, LOG-PREFIX is the exact rational prefix of
;;
;;   log(Y) = 2 * sum_(j>=0) z^(2j+1)/(2j+1),  z=(Y-1)/(Y+1).
;;
;; On all arguments used here, 5 <= Y <= 7 and hence 0 < z <= 3/4. If ETA is
;; positive rational, 8*denominator(ETA) terms make the geometric tail smaller
;; than ETA. SQRT-LOG-APPROX then applies rational bisection on [0,2]. Its
;; logarithm precision and bisection depth make it a regular rational Cauchy
;; name for sqrt(log(Y)), uniformly for 5 <= Y <= 7. MAIN-APPROX consequently
;; is a uniform rational Cauchy name for the exact source integrand on [2,4].

(defun p87b1-positive-rational-p (value)
  (and
   (rationalp value)
   (< 0 value)))

(defun p87b1-effective-precision (precision)
  (if (and
       (p87b1-positive-rational-p precision)
       (< precision 1))
      precision
    1))

(defun p87b1-log-prefix (y terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (1- terms))
           (exponent (+ (* 2 index) 1))
           (ratio (/ (- y 1) (+ y 1))))
      (+ (p87b1-log-prefix y index)
         (/ (* 2 (expt ratio exponent))
            exponent)))))

(defun p87b1-log-terms (precision)
  (if (p87b1-positive-rational-p precision)
      (* 8 (denominator precision))
    1))

(defun p87b1-log-approx (y precision)
  (if (and
       (rationalp y)
       (< 1 y)
       (p87b1-positive-rational-p precision))
      (p87b1-log-prefix
       y
       (p87b1-log-terms precision))
    0))

(defun p87b1-sqrt-bisection
    (radicand steps lower upper)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      lower
    (let ((midpoint (/ (+ lower upper) 2)))
      (if (<= (* midpoint midpoint) radicand)
          (p87b1-sqrt-bisection
           radicand (1- steps) midpoint upper)
        (p87b1-sqrt-bisection
         radicand (1- steps) lower midpoint)))))

(defun p87b1-sqrt-log-approx (y precision)
  (if (and
       (rationalp y)
       (<= 5 y)
       (<= y 7)
       (p87b1-positive-rational-p precision))
      (let* ((eta (p87b1-effective-precision precision))
             (log-precision (/ (* eta eta) 64))
             (radicand
              (p87b1-log-approx y log-precision))
             (steps (* 8 (denominator eta))))
        (p87b1-sqrt-bisection
         radicand steps 0 2))
    0))

(defun p87b1-main-approx (x precision)
  (if (and
       (rationalp x)
       (<= 2 x)
       (<= x 4)
       (p87b1-positive-rational-p precision))
      (let* ((eta (p87b1-effective-precision precision))
             (root-precision (/ eta 1024))
             (left-root
              (p87b1-sqrt-log-approx
               (- 9 x) root-precision))
             (right-root
              (p87b1-sqrt-log-approx
               (+ x 3) root-precision)))
        (/ left-root (+ left-root right-root)))
    0))

;; A tagged piece is (tag left right). A tagged division is an arbitrary
;; finite rational partition of [2,4], with one rational tag in each closed
;; subinterval. No fixed grid, midpoint choice, or finite carrier is used.

(defun p87b1-tagged-piece-p (piece)
  (and
   (true-listp piece)
   (equal (len piece) 3)
   (rationalp (nth 0 piece))
   (rationalp (nth 1 piece))
   (rationalp (nth 2 piece))
   (< (nth 1 piece) (nth 2 piece))
   (<= (nth 1 piece) (nth 0 piece))
   (<= (nth 0 piece) (nth 2 piece))))

(defun p87b1-tagged-division-tail-p
    (division next-left)
  (if (endp division)
      (equal next-left 4)
    (let ((piece (car division)))
      (and
       (p87b1-tagged-piece-p piece)
       (equal (nth 1 piece) next-left)
       (p87b1-tagged-division-tail-p
        (cdr division) (nth 2 piece))))))

(defun p87b1-tagged-division-p (division)
  (and
   (true-listp division)
   (p87b1-tagged-division-tail-p division 2)))

(defun p87b1-mesh-below-p (delta division)
  (if (endp division)
      t
    (let* ((piece (car division))
           (left (nth 1 piece))
           (right (nth 2 piece)))
      (and
       (< (- right left) delta)
       (p87b1-mesh-below-p
        delta (cdr division))))))

(defun p87b1-riemann-sum-approx
    (division epsilon)
  (if (endp division)
      0
    (let* ((piece (car division))
           (tag (nth 0 piece))
           (left (nth 1 piece))
           (right (nth 2 piece))
           (value-precision (/ epsilon 64)))
      (+ (* (p87b1-main-approx tag value-precision)
            (- right left))
         (p87b1-riemann-sum-approx
          (cdr division) epsilon)))))

(defun-sk p87b1-mesh-division-exists-p (delta)
  (exists (division)
    (and
     (p87b1-tagged-division-p division)
     (p87b1-mesh-below-p delta division))))

(defun-sk p87b1-all-mesh-sums-close-p
    (epsilon delta)
  (forall (division)
    (implies
     (and
      (p87b1-tagged-division-p division)
      (p87b1-mesh-below-p delta division))
     (< (abs
         (- (p87b1-riemann-sum-approx
             division epsilon)
            1))
        (* 3/4 epsilon)))))

(defun-sk p87b1-integral-delta-exists-p (epsilon)
  (exists (delta)
    (and
     (p87b1-positive-rational-p delta)
     (p87b1-mesh-division-exists-p delta)
     (p87b1-all-mesh-sums-close-p
      epsilon delta))))

;; Bidirectional equivalence with the source integral:
;;
;; * the atanh prefixes converge uniformly to log on [5,7];
;; * rational bisection and the explicit precision budgets make MAIN-APPROX
;;   converge uniformly to the displayed continuous real integrand on [2,4];
;; * its approximate Riemann sum differs from the exact sum by < epsilon/4;
;; * rational tagged partitions are dense among all tagged partitions, and
;;   uniform continuity makes their all-partitions epsilon-mesh criterion
;;   equivalent in both directions to the ordinary real Riemann integral;
;; * continuity on [2,4] makes that Riemann integral equal to the interval
;;   Lebesgue integral used by Lean and Isabelle.
;;
;; The 3*epsilon/4 margin absorbs the Cauchy-name error in both directions.
;; Thus the predicate below states exactly that the source integral equals 1,
;; rather than asserting a finite quadrature or a rational-domain analogue.

(defun-sk putnambench-putnam-1987-b1-statement ()
  (forall (epsilon)
    (implies
     (p87b1-positive-rational-p epsilon)
     (p87b1-integral-delta-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
