;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_765: every negative integer x whose product with 24
;; has remainder 15 modulo 1199 is at most -449. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-765-statement (x)
  (implies
   (and (integerp x)
        (< x 0)
        (equal (mod (* 24 x) 1199) 15))
   (<= x (- 449))))

(value-triple :itpeval-statement-checked)
:q
