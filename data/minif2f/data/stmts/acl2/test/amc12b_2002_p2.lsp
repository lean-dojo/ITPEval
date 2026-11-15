;; Statement-only formalization of miniF2F corpus artifact amc12b_2002_p2:
;; for every integer x, x = 4 implies
;; (3*x - 2)*(4*x + 1) - (3*x - 2)*(4*x) + 1 = 11. This file contains
;; no proof.

(in-package "ACL2")

(defun amc12b-2002-p2-statement (x)
  (implies (and (integerp x)
                (equal x 4))
           (equal (+ (- (* (- (* 3 x) 2)
                              (+ (* 4 x) 1))
                           (* (- (* 3 x) 2)
                              (* 4 x)))
                        1)
                   11)))

(value-triple :itpeval-statement-checked)
:q
