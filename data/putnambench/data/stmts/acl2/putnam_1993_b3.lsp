;; Statement-only formalization of PutnamBench corpus artifact putnam_1993_b3:
;; the probability that the nearest integer to the ratio of two independent
;; uniform points in (0,1) is even equals 5/4 - pi/4. This file contains no
;; proof.

(in-package "ACL2")

(defun putnam-1993-b3-midpoint (index subdivisions)
  (/ (- (* 2 index) 1)
     (* 2 subdivisions)))

;; FLOOR(x/y + 1/2) is a nearest integer away from the half-integer tie
;; lines. Those countably many lines have planar measure zero.
(defun putnam-1993-b3-event-p (x y)
  (and
   (< 0 x)
   (< x 1)
   (< 0 y)
   (< y 1)
   (evenp (floor (+ (/ x y) 1/2) 1))))

(defun putnam-1993-b3-row-count
    (x remaining subdivisions)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (if
           (putnam-1993-b3-event-p
            x
            (putnam-1993-b3-midpoint
             remaining subdivisions))
           1
         0)
       (putnam-1993-b3-row-count
        x (- remaining 1) subdivisions))))

(defun putnam-1993-b3-event-count
    (remaining subdivisions)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (putnam-1993-b3-row-count
        (putnam-1993-b3-midpoint
         remaining subdivisions)
        subdivisions subdivisions)
       (putnam-1993-b3-event-count
        (- remaining 1) subdivisions))))

;; Direct midpoint sum of the original unit-square event indicator.
(defun putnam-1993-b3-area-approx (subdivisions)
  (if (posp subdivisions)
      (/ (putnam-1993-b3-event-count
          subdivisions subdivisions)
         (* subdivisions subdivisions))
    0))

;; Exact rational Taylor prefixes for arctan(z), used in the independent
;; Machin Cauchy name pi = 16*arctan(1/5) - 4*arctan(1/239).
(defun putnam-1993-b3-arctan-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (exponent (+ (* 2 index) 1))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-1993-b3-arctan-prefix z index)
         (/ (* sign (expt z exponent))
            exponent)))))

(defun putnam-1993-b3-pi-prefix (terms)
  (- (* 16
        (putnam-1993-b3-arctan-prefix 1/5 terms))
     (* 4
        (putnam-1993-b3-arctan-prefix 1/239 terms))))

;; The rational pair (5/4,-1/4) from the source specifies this real value.
(defun putnam-1993-b3-solution-prefix (pi-terms)
  (- 5/4
     (/ (putnam-1993-b3-pi-prefix pi-terms) 4)))

;; The event boundary is a countable union of line segments together with
;; y=0, hence has area zero. The midpoint sums therefore converge to its
;; Lebesgue measure. Existential cutoffs add no proof-specific rate.
(defun-sk putnam-1993-b3-tail-p (epsilon cutoff)
  (forall (precision)
    (implies
     (and
      (natp precision)
      (<= cutoff precision))
     (< (abs
         (- (putnam-1993-b3-area-approx precision)
            (putnam-1993-b3-solution-prefix precision)))
        epsilon))))

(defun-sk putnam-1993-b3-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1993-b3-tail-p epsilon cutoff))))

(defun-sk putnambench-putnam-1993-b3-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1993-b3-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
