;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_302:
;; the square of one half of the imaginary unit is negative one quarter.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-302-statement ()
  (equal (expt (/ #c(0 1) 2) 2)
         (- (/ 1 4))))

(value-triple :itpeval-statement-checked)
:q
