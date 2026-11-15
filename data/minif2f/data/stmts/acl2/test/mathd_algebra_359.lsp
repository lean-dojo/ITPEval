;; Statement-only formalization of miniF2F artifact mathd_algebra_359: for a
;; real number y, the equation (y + 6) + y = 2 * 12 implies y = 9.
;; This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-359-statement (y)
  (implies (and (rationalp y)
                (equal (+ (+ y 6) y) (* 2 12)))
           (equal y 9)))

(value-triple :itpeval-statement-checked)
:q
