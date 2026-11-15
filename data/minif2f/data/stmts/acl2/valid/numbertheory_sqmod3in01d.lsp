;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_sqmod3in01d: for every integer, its square has remainder
;; either 0 or 1 modulo 3. This file contains no proof.

(in-package "ACL2")

(defun numbertheory-sqmod3in01d-statement (a)
  (implies
   (integerp a)
   (or (equal (mod (expt a 2) 3) 0)
       (equal (mod (expt a 2) 3) 1))))

(value-triple :itpeval-statement-checked)
:q
