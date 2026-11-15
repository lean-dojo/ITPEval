;; Statement-only formalization of miniF2F artifact mathd_numbertheory_207: the
;; natural-number equality 8 * 9^2 + 5 * 9 + 2 = 695. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-207 ()
  (equal (+ (+ (* 8 (expt 9 2))
               (* 5 9))
            2)
         695))

(value-triple :itpeval-statement-checked)
:q
