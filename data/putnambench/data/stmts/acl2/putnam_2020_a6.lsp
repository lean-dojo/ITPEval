;; Statement-only formalization of PutnamBench corpus artifact putnam_2020_a6:
;; the least upper bound, over positive integers N and real x, of the given
;; weighted odd-sine sum is pi/4. This file contains no proof.

(in-package "ACL2")

;; A pair (A . B) represents A+B*i. For rational A and B on the unit circle,
;; the imaginary part of (A+B*i)^m is sin(m*x) for some real x. Rational
;; points are dense in the unit circle, and each finite sum below is a
;; continuous polynomial in A and B. Consequently, bounding these rational
;; points is equivalent to bounding the source sum for every real x; this is
;; not a restriction of the real domain to rational x.
(defun putnam-2020-a6-pair-multiply (left right)
  (let ((a (car left))
        (b (cdr left))
        (c (car right))
        (d (cdr right)))
    (cons (- (* a c) (* b d))
          (+ (* a d) (* b c)))))

(defun putnam-2020-a6-pair-power (a b exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (cons 1 0)
    (putnam-2020-a6-pair-multiply
     (cons a b)
     (putnam-2020-a6-pair-power
      a b (- exponent 1)))))

(defun putnam-2020-a6-odd-sine-value (a b index)
  (cdr
   (putnam-2020-a6-pair-power
    a b (+ (* 2 index) 1))))

(defun putnam-2020-a6-weighted-term (n index a b)
  (* (/ (- (+ n (/ 1 2)) index)
        (* (+ n 1) (+ (* 2 index) 1)))
     (putnam-2020-a6-odd-sine-value
      a b index)))

(defun putnam-2020-a6-sum-through (n index a b)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (putnam-2020-a6-weighted-term n 0 a b)
    (+ (putnam-2020-a6-weighted-term
        n index a b)
       (putnam-2020-a6-sum-through
        n (- index 1) a b))))

(defun putnam-2020-a6-weighted-sine-sum (n a b)
  (if (and (integerp n)
           (< 0 n))
      (putnam-2020-a6-sum-through n n a b)
    0))

;; The alternating reciprocal-odd prefixes with 2*K+2 terms increase to
;; pi/4.  Thus a rational q is strictly below pi/4 exactly when it is below
;; one of these prefixes.
(defun putnam-2020-a6-leibniz-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (sign (if (equal (mod index 2) 0)
                     1
                   -1)))
      (+ (putnam-2020-a6-leibniz-prefix index)
         (/ sign (+ (* 2 index) 1))))))

;; This is the strict rational lower cut of the supremum of the source
;; family.  Replacing arbitrary real x by rational points (A,B) on the unit
;; circle does not change this cut: those points are dense, and for each N
;; the displayed finite sum is a continuous polynomial in cos(x),sin(x).
(defun-sk putnam-2020-a6-source-supremum-lower-cut-p (q)
  (exists (n a b)
    (and
     (rationalp q)
     (integerp n)
     (< 0 n)
     (rationalp a)
     (rationalp b)
     (equal (+ (* a a) (* b b)) 1)
     (< q
        (putnam-2020-a6-weighted-sine-sum
         n a b)))))

;; This is the strict rational lower cut of pi/4.
(defun-sk putnam-2020-a6-pi-over-four-lower-cut-p (q)
  (exists (precision)
    (and
     (rationalp q)
     (natp precision)
     (< q
        (putnam-2020-a6-leibniz-prefix
         (+ (* 2 precision) 2))))))

;; Equality on all rational lower cuts is equality of the represented real
;; numbers.  Hence this closed predicate states exactly that the least
;; uniform upper bound of the original f_N(x) is pi/4.
(defun-sk putnambench-putnam-2020-a6-statement ()
  (forall (q)
    (implies
     (rationalp q)
     (iff
      (putnam-2020-a6-source-supremum-lower-cut-p q)
      (putnam-2020-a6-pi-over-four-lower-cut-p q)))))

(value-triple :itpeval-statement-checked)
:q
