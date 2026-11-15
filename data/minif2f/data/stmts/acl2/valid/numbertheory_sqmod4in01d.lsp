;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_sqmod4in01d: every integer square has remainder 0 or 1 modulo
;; 4. This file contains no proof.

(in-package "ACL2")

(defun numbertheory-sqmod4in01d-statement (a)
  (implies
   (integerp a)
   (or (equal (mod (expt a 2) 4) 0)
       (equal (mod (expt a 2) 4) 1))))

(value-triple :itpeval-statement-checked)
:q
