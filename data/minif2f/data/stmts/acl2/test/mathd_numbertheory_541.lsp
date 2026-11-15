;; Statement-only formalization of miniF2F artifact mathd_numbertheory_541:
;; natural numbers m and n greater than 1 whose product is 2005 have sum 406.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-541-statement (m n)
  (implies
   (and (natp m)
        (natp n)
        (< 1 m)
        (< 1 n)
        (equal (* m n) 2005))
   (equal (+ m n) 406)))

(value-triple :itpeval-statement-checked)
:q
