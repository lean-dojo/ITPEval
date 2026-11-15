;; Statement-only formalization of PutnamBench corpus artifact putnam_1988_a1:
;; the real-plane region |x|-|y| <= 1 and |y| <= 1 has area 6. This file
;; contains no proof.

(in-package "ACL2")

(defun putnam-1988-a1-midpoint
    (lower width index subdivisions)
  (+ lower
     (/ (* width (- (* 2 index) 1))
        (* 2 subdivisions))))

(defun putnam-1988-a1-in-region-p (x y)
  (and
   (<= (- (abs x) (abs y)) 1)
   (<= (abs y) 1)))

(defun putnam-1988-a1-row-count
    (x remaining subdivisions)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (if
           (putnam-1988-a1-in-region-p
            x
            (putnam-1988-a1-midpoint
             -1 2 remaining subdivisions))
           1
         0)
       (putnam-1988-a1-row-count
        x (- remaining 1) subdivisions))))

(defun putnam-1988-a1-region-count
    (remaining subdivisions)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (putnam-1988-a1-row-count
        (putnam-1988-a1-midpoint
         -2 4 remaining subdivisions)
        subdivisions subdivisions)
       (putnam-1988-a1-region-count
        (- remaining 1) subdivisions))))

;; The source inequalities imply -2 <= x <= 2 and -1 <= y <= 1. This is the
;; exact midpoint Riemann sum of the original region indicator on that
;; bounding rectangle; no section formula or area computation is embedded.
(defun putnam-1988-a1-area-approx (subdivisions)
  (if (posp subdivisions)
      (/ (* 8
            (putnam-1988-a1-region-count
             subdivisions subdivisions))
         (* subdivisions subdivisions))
    0))

;; The boundary is a finite union of line segments and therefore has area
;; zero, so these indicator sums converge to the source Lebesgue area.
;; Positive rational tolerances are cofinal among positive real tolerances.
(defun-sk putnam-1988-a1-tail-p (epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (natp subdivisions)
      (<= cutoff subdivisions))
     (< (abs
         (- (putnam-1988-a1-area-approx subdivisions)
            6))
        epsilon))))

(defun-sk putnam-1988-a1-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1988-a1-tail-p epsilon cutoff))))

(defun-sk putnambench-putnam-1988-a1-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1988-a1-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
