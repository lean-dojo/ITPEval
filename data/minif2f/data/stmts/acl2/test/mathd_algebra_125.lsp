;; Statement-only formalization of miniF2F artifact mathd_algebra_125: a
;; positive-natural linear system with integer subtraction that determines
;; x = 6. This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-125-statement (x y)
  (implies (and (natp x)
                (natp y)
                (< 0 x)
                (< 0 y)
                (equal (* 5 x) y)
                (equal (+ (- x 3) (- y 3)) 30))
           (equal x 6)))

(value-triple :itpeval-statement-checked)
:q
