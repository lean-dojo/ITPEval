;; Statement-only formalization of PutnamBench corpus artifact putnam_1973_a3:
;; for each positive integer n, the minimum of k + n/k over positive integers
;; has the same integer part as sqrt(4*n + 1). This file contains no proof.

(in-package "ACL2")

;; The source function B is eliminated by its defining minimum. For positive
;; integer N, every integer K > N gives
;;
;;   K + N/K > N + 1 = 1 + N/1,
;;
;; so the unrestricted positive-integer minimum is exactly the minimum over
;; 1 <= K <= N. ACL2 computes these values as exact rationals.
(defun putnam-1973-a3-value (n k)
  (+ k (/ n k)))

(defun putnam-1973-a3-minimum-through (n k)
  (declare (xargs :measure (nfix k)))
  (if (and (integerp k)
           (< 1 k))
      (let ((current (putnam-1973-a3-value n k))
            (previous
             (putnam-1973-a3-minimum-through n (- k 1))))
        (if (< current previous)
            current
          previous))
    (putnam-1973-a3-value n 1)))

;; For natural X, descending from X returns the unique integer M satisfying
;; M^2 <= X < (M+1)^2, hence exactly floor(sqrt(X)). This keeps the source
;; square root internal while preserving its integer part bidirectionally.
(defun putnam-1973-a3-floor-sqrt-down (x candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (if (<= (* candidate candidate) x)
        candidate
      (putnam-1973-a3-floor-sqrt-down
       x (- candidate 1)))))

(defun putnam-1973-a3-floor-sqrt (x)
  (putnam-1973-a3-floor-sqrt-down x x))

(defun putnambench-putnam-1973-a3-statement (n)
  (implies
   (and (integerp n)
        (< 0 n))
   (equal
    (floor (putnam-1973-a3-minimum-through n n) 1)
    (putnam-1973-a3-floor-sqrt (+ (* 4 n) 1)))))

(value-triple :itpeval-statement-checked)
:q
