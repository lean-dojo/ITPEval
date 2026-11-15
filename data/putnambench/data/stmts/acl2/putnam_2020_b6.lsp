;; Statement-only formalization of PutnamBench corpus artifact putnam_2020_b6:
;; the alternating sum from k = 1 through a positive integer n, with exponent
;; floor(k*(sqrt(2)-1)), is nonnegative. This file contains no proof.

(in-package "ACL2")

;; For natural X, descending from X returns the unique natural M satisfying
;; M^2 <= X < (M+1)^2, hence exactly floor(sqrt(X)).
(defun putnam-2020-b6-floor-sqrt-down (x candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp x))
          (not (natp candidate)))
      0
    (if (<= (* candidate candidate) x)
        candidate
      (putnam-2020-b6-floor-sqrt-down
       x (- candidate 1)))))

(defun putnam-2020-b6-floor-sqrt (x)
  (if (natp x)
      (putnam-2020-b6-floor-sqrt-down x x)
    0))

;; For natural K,
;;
;;   floor(K*(sqrt(2)-1))
;;     = floor(K*sqrt(2)) - K
;;     = floor(sqrt(2*K^2)) - K.
;;
;; Thus this natural exponent is exactly the source real-number floor, not a
;; rational approximation to sqrt(2).
(defun putnam-2020-b6-exponent (k)
  (if (natp k)
      (- (putnam-2020-b6-floor-sqrt
          (* 2 k k))
         k)
    0))

;; This is the inclusive sum from k = 1 through UPPER.
(defun putnam-2020-b6-sum-through (upper)
  (declare (xargs :measure (nfix upper)))
  (if (zp upper)
      0
    (+ (putnam-2020-b6-sum-through (- upper 1))
       (expt -1 (putnam-2020-b6-exponent upper)))))

(defun putnambench-putnam-2020-b6-statement (n)
  (implies
   (posp n)
   (<= 0 (putnam-2020-b6-sum-through n))))

(value-triple :itpeval-statement-checked)
:q
