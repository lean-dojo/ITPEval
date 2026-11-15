;; Statement-only formalization of miniF2F corpus artifact amc12b_2002_p3:
;; every positive integer n for which n^2 - 3*n + 2 is prime equals 3.
;; This file contains no proof.

(in-package "ACL2")

(defun amc12b-2002-p3-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (amc12b-2002-p3-no-divisor-from-p n (+ d 1)))
    t))

(defun amc12b-2002-p3-primep (n)
  (and (natp n)
       (< 1 n)
       (amc12b-2002-p3-no-divisor-from-p n 2)))

(defun amc12b-2002-p3-statement (n)
  (implies
   (and (integerp n)
        (< 0 n)
        (amc12b-2002-p3-primep
         (- (+ (* n n) 2)
            (* 3 n))))
   (equal n 3)))

(value-triple :itpeval-statement-checked)
:q
