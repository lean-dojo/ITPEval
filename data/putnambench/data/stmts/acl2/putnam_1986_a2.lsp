;; Statement-only formalization of PutnamBench corpus artifact putnam_1986_a2:
;; the units digit of floor(10^20000 / (10^100 + 3)) is 3.
;; This file contains no proof.

(in-package "ACL2")

(defun putnambench-putnam-1986-a2-statement ()
  (equal
   (mod
    (floor (expt 10 20000)
           (+ (expt 10 100) 3))
    10)
   3))

(value-triple :itpeval-statement-checked)
:q
