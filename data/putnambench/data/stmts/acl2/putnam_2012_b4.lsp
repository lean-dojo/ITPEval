;; Statement-only formalization of PutnamBench corpus artifact putnam_2012_b4:
;; whether the real sequence a_n - ln(n), where a_0 = 1 and
;; a_(n+1) = a_n + exp(-a_n), has a finite limit. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The recurrence uniquely determines the source sequence.  The definitions
;; below give each of its terms concrete exact rational interval names.
;; Exponential bounds come from the positive Taylor series with a geometric
;; remainder bound, and logarithm bounds come from the atanh series
;;
;;   ln(n) = 2 * sum_{j>=0} z^(2*j+1)/(2*j+1),
;;   z = (n-1)/(n+1).
;;
;; Refinement is unbounded.  Thus no real is replaced by a fixed-precision
;; rational, finite table, opaque carrier, or external witness.

(defun p12b4-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (p12b4-factorial (1- n)))))

(defun p12b4-power (base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      1
    (* base
       (p12b4-power base (1- exponent)))))

;; Sum x^j/j! for 0 <= j < TERMS.

(defun p12b4-exp-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((j (1- terms)))
      (+ (p12b4-exp-prefix x j)
         (/ (p12b4-power x j)
            (p12b4-factorial j))))))

;; For nonnegative rational X, this count is strictly larger than X and
;; tends to infinity with PRECISION.

(defun p12b4-exp-term-count (x precision)
  (+ 2
     (nfix precision)
     (if (rationalp x)
         (abs (numerator x))
       0)))

;; If TERMS > X >= 0, the omitted Taylor tail is at most
;;
;;   (x^terms/terms!) / (1 - x/(terms+1)).

(defun p12b4-exp-tail-bound (x terms)
  (let* ((first-omitted
          (/ (p12b4-power x terms)
             (p12b4-factorial terms)))
         (ratio (/ x (+ terms 1))))
    (/ first-omitted (- 1 ratio))))

(defun p12b4-exp-positive-lower (x precision)
  (let ((terms
         (p12b4-exp-term-count x precision)))
    (p12b4-exp-prefix x terms)))

(defun p12b4-exp-positive-upper (x precision)
  (let ((terms
         (p12b4-exp-term-count x precision)))
    (+ (p12b4-exp-prefix x terms)
       (p12b4-exp-tail-bound x terms))))

;; Reciprocal interval bounds for exp(-X), with X nonnegative.

(defun p12b4-exp-negative-lower (x precision)
  (/ 1 (p12b4-exp-positive-upper x precision)))

(defun p12b4-exp-negative-upper (x precision)
  (/ 1 (p12b4-exp-positive-lower x precision)))

;; Concrete rational enclosures of the uniquely determined a_n.  Monotonicity
;; of x |-> exp(-x) reverses the endpoints in the exponential summand.

(mutual-recursion
 (defun p12b4-a-lower (n precision)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       1
     (let* ((previous (1- n))
            (inner-precision
             (+ (nfix precision) (nfix n)))
            (lower
             (p12b4-a-lower
              previous inner-precision))
            (upper
             (p12b4-a-upper
              previous inner-precision)))
       (+ lower
          (p12b4-exp-negative-lower
           upper inner-precision)))))
 (defun p12b4-a-upper (n precision)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       1
     (let* ((previous (1- n))
            (inner-precision
             (+ (nfix precision) (nfix n)))
            (lower
             (p12b4-a-lower
              previous inner-precision))
            (upper
             (p12b4-a-upper
              previous inner-precision)))
       (+ upper
          (p12b4-exp-negative-upper
           lower inner-precision))))))

;; Sum the first TERMS terms of the exact atanh series for ln(N).

(defun p12b4-log-z (n)
  (if (posp n)
      (/ (- n 1) (+ n 1))
    0))

(defun p12b4-log-prefix-aux (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((j (1- terms))
           (degree (+ (* 2 j) 1)))
      (+ (p12b4-log-prefix-aux z j)
         (/ (* 2
               (p12b4-power z degree))
            degree)))))

(defun p12b4-log-prefix (n terms)
  (if (posp n)
      (p12b4-log-prefix-aux
       (p12b4-log-z n) terms)
    0))

;; Dropping the denominators 2*j+1 bounds the remaining positive series by
;; a geometric tail.  This is zero at N=1 and tends to zero for every fixed
;; positive N.

(defun p12b4-log-tail-bound (n terms)
  (if (posp n)
      (let* ((z (p12b4-log-z n))
             (degree (+ (* 2 (nfix terms)) 1)))
        (/ (* 2 (p12b4-power z degree))
           (- 1 (p12b4-power z 2))))
    0))

(defun p12b4-log-lower (n precision)
  (p12b4-log-prefix
   n (+ 1 (nfix precision))))

(defun p12b4-log-upper (n precision)
  (let ((terms (+ 1 (nfix precision))))
    (+ (p12b4-log-prefix n terms)
       (p12b4-log-tail-bound n terms))))

;; Rational interval names for a_n - ln(n).  At n=0, LOG-LOWER and
;; LOG-UPPER are both zero, matching the totalized logarithm in the formal
;; ground-truth statements.

(defun p12b4-difference-lower (n precision)
  (- (p12b4-a-lower n precision)
     (p12b4-log-upper n precision)))

(defun p12b4-difference-upper (n precision)
  (- (p12b4-a-upper n precision)
     (p12b4-log-lower n precision)))

;; A strict distance bound between two exact interval-named reals holds when
;; some finite refinement certifies both directed endpoint inequalities.
;; Because all bounds shrink to their exact denotations, this is equivalent
;; to |(a_m-ln m) - (a_n-ln n)| < EPSILON over the real numbers.

(defun p12b4-close-at-refinement-p
    (m n epsilon refinement)
  (let ((m-lower
         (p12b4-difference-lower
          m refinement))
        (m-upper
         (p12b4-difference-upper
          m refinement))
        (n-lower
         (p12b4-difference-lower
          n refinement))
        (n-upper
         (p12b4-difference-upper
          n refinement)))
    (and
     (< (- m-upper n-lower) epsilon)
     (< (- n-upper m-lower) epsilon))))

(defun-sk p12b4-exact-close-p (m n epsilon)
  (exists (refinement)
    (and
     (natp refinement)
     (p12b4-close-at-refinement-p
      m n epsilon refinement))))

(defun-sk p12b4-cauchy-tail-p (epsilon cutoff)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (natp cutoff)
      (<= cutoff m)
      (<= cutoff n))
     (p12b4-exact-close-p m n epsilon))))

(defun-sk p12b4-cauchy-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p12b4-cauchy-tail-p
      epsilon cutoff))))

;; A real sequence has a finite real limit exactly when it is Cauchy.
;; Quantifying over every positive rational epsilon is equivalent to
;; quantifying over every positive real epsilon, by density of the rationals.
;; This keeps the limit and cutoff content internal without restricting the
;; putative limit to an ACL2 rational.

(defun-sk p12b4-finite-limit-exists-p ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (p12b4-cauchy-cutoff-exists-p
      epsilon))))

(defun putnambench-acl2-putnam-2012-b4-statement ()
  ;; The published answer to the source's yes/no question is True.
  (p12b4-finite-limit-exists-p))

(value-triple :itpeval-statement-checked)
:q
