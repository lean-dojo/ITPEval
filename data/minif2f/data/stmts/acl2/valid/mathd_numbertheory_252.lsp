;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_252:
;; seven factorial has remainder 3 modulo 23. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-252-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (mathd-numbertheory-252-factorial (- n 1)))))

(defun mathd-numbertheory-252-statement ()
  (equal (mod (mathd-numbertheory-252-factorial 7) 23)
         3))

(value-triple :itpeval-statement-checked)
:q
