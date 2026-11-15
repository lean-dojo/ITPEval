;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_739: the factorial of 9 has remainder 0 modulo 10.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-739-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (mathd-numbertheory-739-factorial (- n 1)))))

(defun mathd-numbertheory-739-statement ()
  (equal (mod (mathd-numbertheory-739-factorial 9) 10)
         0))

(value-triple :itpeval-statement-checked)
:q
