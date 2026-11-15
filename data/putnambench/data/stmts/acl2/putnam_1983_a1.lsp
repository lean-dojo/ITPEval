;; Statement-only formalization of PutnamBench corpus artifact putnam_1983_a1:
;; exactly 2301 positive integers divide at least one of 10^40 and 20^30.
;; This file contains no proof.

(in-package "ACL2")

;; Every positive divisor of either fixed number is at most that number, and
;; 20^30 < 10^40. Thus counting through 10^40 is exactly the cardinality of
;; the source set, not a restriction of its domain.
(defun putnam-1983-a1-divisor-of-either-p (n)
  (and
   (posp n)
   (or (equal (mod (expt 10 40) n) 0)
       (equal (mod (expt 20 30) n) 0))))

(defun putnam-1983-a1-count-through (candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (+ (if (putnam-1983-a1-divisor-of-either-p candidate)
           1
         0)
       (putnam-1983-a1-count-through (- candidate 1)))))

(defun putnambench-putnam-1983-a1-statement ()
  (equal
   (putnam-1983-a1-count-through (expt 10 40))
   2301))

(value-triple :itpeval-statement-checked)
:q
