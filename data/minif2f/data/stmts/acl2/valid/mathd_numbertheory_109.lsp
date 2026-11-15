;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_109: the sum of v(k) for k = 1 through 100, where
;; v(n) = 2*n - 1 with natural subtraction, has remainder 4 modulo 7.
;; This file contains no proof.
;;
;; The source hypothesis uniquely determines v on every natural number.
;; The function below is exactly that natural-valued function, including
;; v(0) = 0, so eliminating the universally quantified function parameter
;; is bidirectionally equivalent to the source implication.

(in-package "ACL2")

(defun mathd-numbertheory-109-value (n)
  (if (natp n)
      (nfix (- (* 2 n) 1))
    0))

(defun mathd-numbertheory-109-sum-from (start remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (mathd-numbertheory-109-value start)
       (mathd-numbertheory-109-sum-from
        (+ start 1)
        (- remaining 1)))))

(defun mathd-numbertheory-109-statement ()
  (equal
   (mod (mathd-numbertheory-109-sum-from 1 100) 7)
   4))

(value-triple :itpeval-statement-checked)
:q
