;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__068, "Sum of an Arithmetic Series": for all
;; natural numbers a, d, and n, twice the inclusive sum from i = 0 through n
;; of a + i*d equals (n + 1) times (2*a + n*d). This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-068-arithmetic-series-sum-through (a d n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      a
    (+ (hundred-theorems-068-arithmetic-series-sum-through
        a d (- n 1))
       (+ a (* n d)))))

(defun hundred-theorems-068-sum-of-an-arithmetic-series-statement
    (a d n)
  (implies
   (and (natp a)
        (natp d)
        (natp n))
   (equal
    (* 2
       (hundred-theorems-068-arithmetic-series-sum-through a d n))
    (* (+ n 1)
       (+ (* 2 a)
          (* n d))))))

(value-triple :itpeval-statement-checked)
:q
