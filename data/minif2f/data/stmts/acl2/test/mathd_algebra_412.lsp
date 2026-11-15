;; Statement-only formalization of miniF2F corpus artifact
;; mathd_algebra_412: two linear equations over real numbers imply x = 18.
;; This file contains no proof.
;;
;; ACL2 exact rational arithmetic is bidirectionally equivalent here. Adding
;; and subtracting the equations gives x = 18 and y = 7, so every real
;; assignment satisfying the hypotheses is rational; every rational assignment
;; embeds into the reals with the same equations and conclusion.

(in-package "ACL2")

(defun mathd-algebra-412-statement (x y)
  (implies
   (and (rationalp x)
        (rationalp y)
        (equal (+ x y) 25)
        (equal (- x y) 11))
   (equal x 18)))

(value-triple :itpeval-statement-checked)
:q
