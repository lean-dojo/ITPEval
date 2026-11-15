;; Statement-only formalization of miniF2F artifact mathd_algebra_296: the
;; absolute value of the integer expression (3491 - 60) * (3491 + 60) -
;; 3491^2 equals 3600. This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-296-statement ()
  (equal (abs (- (* (- 3491 60)
                    (+ 3491 60))
                 (expt 3491 2)))
         3600))

(value-triple :itpeval-statement-checked)
:q
