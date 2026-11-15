;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_457: if a positive natural number n has 80325 dividing
;; n factorial, then n is at least 17. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-457-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (mathd-numbertheory-457-factorial (- n 1)))))

(defun mathd-numbertheory-457-statement (n)
  (implies
   (and (natp n)
        (< 0 n)
        (equal (mod (mathd-numbertheory-457-factorial n) 80325)
               0))
   (<= 17 n)))

(value-triple :itpeval-statement-checked)
:q
