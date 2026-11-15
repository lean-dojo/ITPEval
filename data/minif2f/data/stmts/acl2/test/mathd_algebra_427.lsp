;; Statement-only formalization of miniF2F artifact mathd_algebra_427: for
;; real numbers x, y, and z, three linear equations imply x + y + z = 12.
;; This file contains no proof.
;; ACL2-NUMBERP is equivalent for this implication: over any characteristic-
;; zero field, the antecedent uniquely forces x = 66/13, y = 23/13, and
;; z = 67/13, so every satisfying ACL2-number tuple is rational and real.

(in-package "ACL2")

(defun mathd-algebra-427-statement (x y z)
  (implies
   (and (acl2-numberp x)
        (acl2-numberp y)
        (acl2-numberp z)
        (equal (+ (* 3 x) y) 17)
        (equal (+ (* 5 y) z) 14)
        (equal (+ (* 3 x) (* 5 z)) 41))
   (equal (+ (+ x y) z) 12)))

(value-triple :itpeval-statement-checked)
:q
