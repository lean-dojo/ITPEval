;; Statement-only formalization of miniF2F corpus artifact amc12b_2004_p3:
;; for natural numbers x and y, if 2^x * 3^y = 1296, then x + y = 8.
;; This file contains no proof.

(in-package "ACL2")

(defun amc12b-2004-p3-statement (x y)
  (implies
   (and (natp x)
        (natp y)
        (equal (* (expt 2 x)
                  (expt 3 y))
               1296))
   (equal (+ x y) 8)))

(value-triple :itpeval-statement-checked)
:q
