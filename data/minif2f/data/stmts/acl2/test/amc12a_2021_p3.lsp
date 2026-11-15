;; Statement-only formalization of miniF2F corpus artifact amc12a_2021_p3:
;; for natural numbers x and y, a sum of 17402, divisibility of x by 10, and
;; x divided by 10 equaling y imply the integer difference x - y is 14238.
;; This file contains no proof.

(in-package "ACL2")

(defun amc12a-2021-p3-statement (x y)
  (implies
   (and (natp x)
        (natp y)
        (equal (+ x y) 17402)
        (equal (mod x 10) 0)
        (equal (floor x 10) y))
   (equal (- x y) 14238)))

(value-triple :itpeval-statement-checked)
:q
