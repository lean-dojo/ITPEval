;; Statement-only formalization of PutnamBench corpus artifact putnam_1993_a1:
;; for c = 4/9, the horizontal line y = c cuts y = 2*x - 3*x^3 so that the
;; two specified first-quadrant shaded areas are equal. This file contains no
;; proof.

(in-package "ACL2")

(defun putnam-1993-a1-isqrt-search (x candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp x))
          (not (natp candidate)))
      0
    (if (<= (* candidate candidate) x)
        candidate
      (putnam-1993-a1-isqrt-search
       x (- candidate 1)))))

(defun putnam-1993-a1-isqrt (x)
  (if (natp x)
      (putnam-1993-a1-isqrt-search x x)
    0))

;; A rational upper approximation to sqrt(X), converging as SCALE grows.
(defun putnam-1993-a1-sqrt-upper (x scale)
  (if (and (rationalp x)
           (<= 0 x)
           (posp scale))
      (/ (+ 1
            (putnam-1993-a1-isqrt
             (floor (* x scale scale) 1)))
         scale)
    0))

(defun putnam-1993-a1-solution ()
  4/9)

(defun putnam-1993-a1-cubic (x)
  (- (* 2 x) (* 3 (expt x 3))))

(defun putnam-1993-a1-positive-part (x)
  (if (< 0 x) x 0))

(defun putnam-1993-a1-midpoint
    (upper index subdivisions)
  (/ (* upper (- (* 2 index) 1))
     (* 2 subdivisions)))

(defun putnam-1993-a1-integrand
    (c x left-p)
  (if left-p
      (putnam-1993-a1-positive-part
       (- c (putnam-1993-a1-cubic x)))
    (putnam-1993-a1-positive-part
     (- (putnam-1993-a1-cubic x) c))))

(defun putnam-1993-a1-integral-sum
    (c upper remaining subdivisions left-p)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (putnam-1993-a1-integrand
        c
        (putnam-1993-a1-midpoint
         upper remaining subdivisions)
        left-p)
       (putnam-1993-a1-integral-sum
        c upper (- remaining 1)
        subdivisions left-p))))

;; Direct midpoint approximation to one of the two source positive-part
;; integrals. RADICAND is 2 on the left and 6 on the right.
(defun putnam-1993-a1-integral-approx
    (c radicand precision left-p)
  (if (posp precision)
      (let ((upper
             (/ (putnam-1993-a1-sqrt-upper
                 radicand precision)
                3)))
        (* (/ upper precision)
           (putnam-1993-a1-integral-sum
            c upper precision precision left-p)))
    0))

;; With c positive, c < 4*sqrt(2)/9 is equivalent to 81*c^2 < 32.
(defun putnam-1993-a1-below-cubic-maximum-p (c)
  (and (rationalp c)
       (< 0 c)
       (< (* 81 c c) 32)))

;; The endpoint approximations and midpoint sums converge jointly to the two
;; source integrals. The positive-part integrands are continuous, so no roots
;; or antiderivative computations are embedded in the statement.
(defun-sk putnam-1993-a1-area-tail-p
    (c epsilon cutoff)
  (forall (precision)
    (implies
     (and
      (natp precision)
      (<= cutoff precision))
     (< (abs
         (- (putnam-1993-a1-integral-approx
             c 2 precision t)
            (putnam-1993-a1-integral-approx
             c 6 precision nil)))
        epsilon))))

(defun-sk putnam-1993-a1-area-cutoff-exists-p
    (c epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1993-a1-area-tail-p
      c epsilon cutoff))))

(defun-sk putnam-1993-a1-areas-equal-p (c)
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1993-a1-area-cutoff-exists-p
      c epsilon))))

(defun putnambench-putnam-1993-a1-statement ()
  (let ((c (putnam-1993-a1-solution)))
    (and
     (< 0 c)
     (putnam-1993-a1-below-cubic-maximum-p c)
     (putnam-1993-a1-areas-equal-p c))))

(value-triple :itpeval-statement-checked)
:q
