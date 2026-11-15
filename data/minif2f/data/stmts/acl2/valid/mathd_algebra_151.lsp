;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_151:
;; the ceiling of the real square root of 27 minus the floor of the real
;; square root of 26 equals 1. This file contains no proof.

(in-package "ACL2")

;; For a natural N, descending from N returns the unique integer K satisfying
;; K^2 <= N < (K+1)^2, exactly floor(sqrt(N)) for the principal real square
;; root. The ceiling is K for a perfect square and K+1 otherwise, exactly
;; ceiling(sqrt(N)). Thus these integer functions eliminate only the
;; intermediate irrational values and preserve both source operations.
(defun mathd-algebra-151-floor-sqrt-down (n candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (if (<= (* candidate candidate) n)
        candidate
      (mathd-algebra-151-floor-sqrt-down
       n (- candidate 1)))))

(defun mathd-algebra-151-floor-sqrt (n)
  (mathd-algebra-151-floor-sqrt-down n n))

(defun mathd-algebra-151-ceil-sqrt (n)
  (let ((floor-root (mathd-algebra-151-floor-sqrt n)))
    (if (equal (* floor-root floor-root) n)
        floor-root
      (+ floor-root 1))))

(defun mathd-algebra-151-statement ()
  (equal
   (- (mathd-algebra-151-ceil-sqrt 27)
      (mathd-algebra-151-floor-sqrt 26))
   1))

(value-triple :itpeval-statement-checked)
:q
