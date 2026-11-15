;; Statement-only formalization of PutnamBench corpus artifact putnam_1997_b1:
;; for every positive integer n, the sum from m = 1 through 6n-1 of the
;; minimum nearest-integer distances of m/(6n) and m/(3n) equals n. This file
;; contains no proof.

(in-package "ACL2")

(defun putnam-1997-b1-min (left right)
  (if (<= left right)
      left
    right))

;; Every argument used below is rational. ACL2's exact rational FLOOR gives
;; the two adjacent integers, so the smaller absolute difference is exactly
;; the source's distance to the nearest integer, including half-integer ties.
(defun putnam-1997-b1-distance-to-integer (x)
  (let ((lower (floor x 1))
        (upper (floor (+ x 1) 1)))
    (putnam-1997-b1-min
     (abs (- x lower))
     (abs (- x upper)))))

(defun putnam-1997-b1-sum-through (n m)
  (declare (xargs :measure (nfix m)))
  (if (zp m)
      0
    (+ (putnam-1997-b1-sum-through n (- m 1))
       (putnam-1997-b1-min
        (putnam-1997-b1-distance-to-integer
         (/ m (* 6 n)))
        (putnam-1997-b1-distance-to-integer
         (/ m (* 3 n)))))))

;; Substituting the source hypothesis that defines F yields this equivalent
;; pointwise identity.
(defun putnambench-putnam-1997-b1-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal
    (putnam-1997-b1-sum-through n (- (* 6 n) 1))
    n)))

(value-triple :itpeval-statement-checked)
:q
