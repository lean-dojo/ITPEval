;; Statement-only formalization of miniF2F corpus artifact induction_sum_odd:
;; for every natural number n, the sum of the odd numbers 2*k + 1 for
;; k = 0 through n - 1 equals n squared. This file contains no proof.

(in-package "ACL2")

(defun induction-sum-odd-sum (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (induction-sum-odd-sum (- n 1))
       (+ (* 2 (- n 1)) 1))))

(defun induction-sum-odd-statement (n)
  (implies (natp n)
           (equal (induction-sum-odd-sum n)
                  (* n n))))

(value-triple :itpeval-statement-checked)
:q
