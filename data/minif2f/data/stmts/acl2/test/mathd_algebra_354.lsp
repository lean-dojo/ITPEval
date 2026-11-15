;; Statement-only formalization of miniF2F corpus artifact
;; mathd_algebra_354: two linear equations over real numbers imply that
;; a + 20 * d = 135. This file contains no proof.
;;
;; ACL2 exact rational arithmetic is bidirectionally equivalent here.
;; Subtracting the two equations gives d = 15/2, and substitution gives
;; a = -15, so every real solution is rational; every rational solution
;; also embeds into the reals with the same equations and conclusion.

(in-package "ACL2")

(defun mathd-algebra-354-statement (a d)
  (implies
   (and (rationalp a)
        (rationalp d)
        (equal (+ a (* 6 d)) 30)
        (equal (+ a (* 10 d)) 60))
   (equal (+ a (* 20 d)) 135)))

(value-triple :itpeval-statement-checked)
:q
