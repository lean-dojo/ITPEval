;; Statement-only formalization of Logipedia corpus artifact nat.le_pred_n,
;; catalog title "nat.le_pred_n": the natural-number predecessor of every
;; natural number is less than or equal to that number. This file contains no
;; proof.

(in-package "ACL2")

(defun logipedia-nat-le-pred-n-predecessor (n)
  (if (zp n)
      0
    (- n 1)))

(defun logipedia-nat-le-pred-n-statement (n)
  (implies
   (natp n)
   (<= (logipedia-nat-le-pred-n-predecessor n)
       n)))

(value-triple :itpeval-statement-checked)
:q
