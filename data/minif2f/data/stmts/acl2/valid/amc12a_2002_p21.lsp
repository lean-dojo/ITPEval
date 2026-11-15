;; Statement-only formalization of miniF2F corpus artifact amc12a_2002_p21:
;; for every natural sequence with initial values 4 and 7 whose equation
;; u(n+2) = (u(n) + u(n+1)) mod 10 holds for every natural n, a sum above
;; 10000 among its first n terms implies n >= 1999. This file contains no
;; proof.
;;
;; The source hypotheses determine the sequence uniquely, so the recursive
;; definition below eliminates the function parameter without adding free
;; intermediate values.

(in-package "ACL2")

(defun amc12a-2002-p21-sequence (n)
  (declare (xargs :measure (nfix n)))
  (if (not (natp n))
      0
    (cond ((equal n 0) 4)
          ((equal n 1) 7)
          (t
           (mod (+ (amc12a-2002-p21-sequence (- n 2))
                   (amc12a-2002-p21-sequence (- n 1)))
                10)))))

(defun amc12a-2002-p21-prefix-sum (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (amc12a-2002-p21-prefix-sum (- n 1))
       (amc12a-2002-p21-sequence (- n 1)))))

(defun amc12a-2002-p21-statement (n)
  (implies
   (and (natp n)
        (> (amc12a-2002-p21-prefix-sum n)
           10000))
   (<= 1999 n)))

(value-triple :itpeval-statement-checked)
:q
