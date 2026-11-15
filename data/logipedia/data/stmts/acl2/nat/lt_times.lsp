;; Statement-only formalization of Logipedia corpus artifact nat.lt_times:
;; for natural numbers n < m and p < q, the product n*p is less than m*q.
;; This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-lt-times-statement (n m p q)
  (implies
   (and (natp n)
        (natp m)
        (natp p)
        (natp q)
        (< n m)
        (< p q))
   (< (* n p)
      (* m q))))

(value-triple :itpeval-statement-checked)
:q
