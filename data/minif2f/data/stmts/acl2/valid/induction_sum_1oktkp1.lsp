;; Statement-only formalization of miniF2F corpus artifact
;; induction_sum_1oktkp1: for every natural number n, the real sum of
;; 1/((k+1)*(k+2)) over 0 <= k < n equals n/(n+1). ACL2 computes these
;; rational quantities exactly, and equality is unchanged by their canonical
;; embedding into the reals. This file contains no proof.

(in-package "ACL2")

(defun induction-sum-1oktkp1-sum (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (induction-sum-1oktkp1-sum (- n 1))
       (/ 1 (* n (+ n 1))))))

(defun induction-sum-1oktkp1-statement (n)
  (implies
   (natp n)
   (equal
    (induction-sum-1oktkp1-sum n)
    (/ n (+ n 1)))))

(value-triple :itpeval-statement-checked)
:q
