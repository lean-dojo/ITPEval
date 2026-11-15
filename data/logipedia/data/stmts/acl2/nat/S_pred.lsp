;; Statement-only formalization of Logipedia corpus artifact nat.S_pred,
;; catalog title "nat.S_pred": every positive natural number equals the
;; successor of its natural-number predecessor. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-s-pred-predecessor (n)
  (if (zp n)
      0
    (- n 1)))

(defun logipedia-nat-s-pred-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal (+ 1 (logipedia-nat-s-pred-predecessor n))
          n)))

(value-triple :itpeval-statement-checked)
:q
