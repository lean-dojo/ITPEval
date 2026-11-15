;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_343: the product of 2*k+1 over the natural indices
;; k = 0 through 5 has remainder 5 modulo 10. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-343-odd-product (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (mathd-numbertheory-343-odd-product (- n 1))
       (+ (* 2 (- n 1)) 1))))

(defun mathd-numbertheory-343-statement ()
  (equal (mod (mathd-numbertheory-343-odd-product 6) 10)
         5))

(value-triple :itpeval-statement-checked)
:q
