;; Statement-only formalization of PutnamBench corpus artifact putnam_1994_b1:
;; the positive integers within 250 of exactly 15 natural-number squares are
;; precisely 315 through 325 and 332 through 350. This file contains no proof.

(in-package "ACL2")

;; For positive integer n, every natural m satisfying |n - m^2| <= 250 has
;; m^2 <= n + 250, hence m <= n + 250. Thus this recursion counts the entire
;; source set of natural-number square roots, including m = 0.
(defun putnam-1994-b1-square-count-through (n m)
  (declare (xargs :measure (nfix m)))
  (if (and (integerp n)
           (natp m))
      (if (zp m)
          (if (<= (abs n) 250)
              1
            0)
        (+ (if (<= (abs (- n (* m m))) 250)
               1
             0)
           (putnam-1994-b1-square-count-through
            n (- m 1))))
    0))

(defun putnam-1994-b1-solution-p (n)
  (and
   (integerp n)
   (or (and (<= 315 n)
            (<= n 325))
       (and (<= 332 n)
            (<= n 350)))))

(defun putnambench-putnam-1994-b1-statement (n)
  (implies
   (integerp n)
   (iff
    (putnam-1994-b1-solution-p n)
    (and
     (< 0 n)
     (equal
      (putnam-1994-b1-square-count-through
       n (+ n 250))
      15)))))

(value-triple :itpeval-statement-checked)
:q
