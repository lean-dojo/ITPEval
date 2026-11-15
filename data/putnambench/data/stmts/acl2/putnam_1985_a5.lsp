;; Statement-only formalization of PutnamBench corpus artifact putnam_1985_a5:
;; the integral from 0 to 2*pi of the product of cos(k*x), for 1 <= k <= m,
;; is nonzero exactly for m in {3, 4, 7, 8} among 1 <= m <= 10. This file
;; contains no proof.

(in-package "ACL2")

;; Standard ACL2 has exact rationals rather than primitive completed reals.
;; The functions below give the source integral a canonical rational Cauchy
;; name: Machin prefixes approximate pi, Taylor prefixes approximate cosine,
;; and midpoint sums approximate the finite-interval integral. Using one
;; precision parameter is a cofinal diagonal through these three limits.

(defun putnam-1985-a5-arctan-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (+ (* 2 index) 1))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-1985-a5-arctan-prefix z index)
         (/ (* sign (expt z degree))
            degree)))))

(defun putnam-1985-a5-pi-prefix (terms)
  (- (* 16
        (putnam-1985-a5-arctan-prefix (/ 1 5) terms))
     (* 4
        (putnam-1985-a5-arctan-prefix (/ 1 239) terms))))

(defun putnam-1985-a5-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-1985-a5-factorial (- n 1)))))

(defun putnam-1985-a5-cosine-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (degree (* 2 index))
           (sign (if (equal (mod index 2) 0) 1 -1)))
      (+ (putnam-1985-a5-cosine-prefix x index)
         (/ (* sign (expt x degree))
            (putnam-1985-a5-factorial degree))))))

(defun putnam-1985-a5-cosine-product
    (m x cosine-terms)
  (declare (xargs :measure (nfix m)))
  (if (zp m)
      1
    (* (putnam-1985-a5-cosine-prefix
        (* m x) cosine-terms)
       (putnam-1985-a5-cosine-product
        (- m 1) x cosine-terms))))

(defun putnam-1985-a5-grid-point
    (index pi-value subdivisions)
  (/ (* 2 pi-value (+ (* 2 index) 1))
     (* 2 subdivisions)))

(defun putnam-1985-a5-midpoint-sum
    (remaining m pi-value subdivisions cosine-terms)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((index (- remaining 1))
           (x (putnam-1985-a5-grid-point
               index pi-value subdivisions)))
      (+ (putnam-1985-a5-cosine-product
          m x cosine-terms)
         (putnam-1985-a5-midpoint-sum
          index m pi-value subdivisions cosine-terms)))))

(defun putnam-1985-a5-integral-approx (m precision)
  (if (posp precision)
      (let ((pi-value
             (putnam-1985-a5-pi-prefix precision)))
        (* (/ (* 2 pi-value) precision)
           (putnam-1985-a5-midpoint-sum
            precision m pi-value precision precision)))
    0))

;; A convergent real Cauchy name represents a nonzero value exactly when its
;; absolute value is eventually bounded below by a positive rational margin.

(defun-sk putnam-1985-a5-bounded-away-tail-p
    (m margin cutoff)
  (forall (precision)
    (implies
     (and
      (natp precision)
      (<= cutoff precision))
     (< margin
        (abs
         (putnam-1985-a5-integral-approx
          m precision))))))

(defun-sk putnam-1985-a5-integral-nonzero-p (m)
  (exists (margin cutoff)
    (and
     (rationalp margin)
     (< 0 margin)
     (posp cutoff)
     (putnam-1985-a5-bounded-away-tail-p
      m margin cutoff))))

(defun putnam-1985-a5-solution-p (m)
  (or (equal m 3)
      (equal m 4)
      (equal m 7)
      (equal m 8)))

(defun putnambench-putnam-1985-a5-statement (m)
  (iff
   (and
    (natp m)
    (<= 1 m)
    (<= m 10)
    (putnam-1985-a5-integral-nonzero-p m))
   (putnam-1985-a5-solution-p m)))

(value-triple :itpeval-statement-checked)
:q
