;; Statement-only formalization of PutnamBench corpus artifact putnam_1998_b5:
;; the thousandth digit after the decimal point of the square root of the
;; 1998-digit decimal repunit is 1. This file contains no proof.

(in-package "ACL2")

;; This is sum_{i=0}^{digits-1} 10^i, matching the source definition of N.
(defun putnam-1998-b5-repunit-sum (digits)
  (declare (xargs :measure (nfix digits)))
  (if (zp digits)
      0
    (+ (expt 10 (- digits 1))
       (putnam-1998-b5-repunit-sum (- digits 1)))))

;; For natural X, descending from X returns the unique natural M satisfying
;; M^2 <= X < (M+1)^2, hence exactly floor(sqrt(X)).
(defun putnam-1998-b5-isqrt-search (x candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp x))
          (not (natp candidate)))
      0
    (if (<= (* candidate candidate) x)
        candidate
      (putnam-1998-b5-isqrt-search
       x (- candidate 1)))))

(defun putnam-1998-b5-isqrt (x)
  (if (natp x)
      (putnam-1998-b5-isqrt-search x x)
    0))

;; Since 10^1000 is positive,
;;
;;   floor(10^1000 * sqrt(N))
;;     = floor(sqrt(N * 10^2000)).
;;
;; Thus this exact integer computation is bidirectionally equivalent to the
;; source real square-root floor; it does not approximate or restrict it.
(defun putnam-1998-b5-scaled-root-floor (n)
  (if (natp n)
      (putnam-1998-b5-isqrt
       (* n (expt 10 2000)))
    0))

(defun putnambench-putnam-1998-b5-statement (n)
  (implies
   (and (natp n)
        (equal n (putnam-1998-b5-repunit-sum 1998)))
   (equal
    (mod (putnam-1998-b5-scaled-root-floor n) 10)
    1)))

(value-triple :itpeval-statement-checked)
:q
