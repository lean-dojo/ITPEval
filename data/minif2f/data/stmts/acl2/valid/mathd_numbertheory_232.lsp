;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_232:
;; canonical residues x, y, and z modulo 31 satisfying the stated modular
;; inverse equations must have z equal to 29. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-232-statement (x y z)
  (implies
   (and (integerp x)
        (integerp y)
        (integerp z)
        (<= 0 x)
        (< x 31)
        (<= 0 y)
        (< y 31)
        (<= 0 z)
        (< z 31)
        (equal (mod (* x 3) 31) 1)
        (equal (mod (* y 5) 31) 1)
        (equal (mod (* z (+ x y)) 31) 1))
   (equal z 29)))

(value-triple :itpeval-statement-checked)
:q
