;; Statement-only formalization of miniF2F corpus artifact amc12a_2015_p10:
;; integers x and y satisfying 0 < y < x and x + y + x*y = 80 must have
;; x = 26. This file contains no proof.

(in-package "ACL2")

(defun amc12a-2015-p10-statement (x y)
  (implies (and (integerp x)
                (integerp y)
                (< 0 y)
                (< y x)
                (equal (+ (+ x y)
                          (* x y))
                       80))
           (equal x 26)))

(value-triple :itpeval-statement-checked)
:q
