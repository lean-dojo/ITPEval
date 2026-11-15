;; Statement-only formalization of miniF2F corpus artifact
;; mathd_algebra_338: three linear equations over real numbers imply that
;; the product of the three unknowns is -56. This file contains no proof.
;;
;; ACL2 exact rational arithmetic is bidirectionally equivalent here.
;; Subtracting consecutive equations gives b = a + 6 and c = b + 5;
;; substitution into the first equation gives a = -4, b = 2, and c = 7.
;; Thus every real solution is rational, while every rational solution embeds
;; into the reals with the same equations and conclusion.

(in-package "ACL2")

(defun mathd-algebra-338-statement (a b c)
  (implies
   (and (rationalp a)
        (rationalp b)
        (rationalp c)
        (equal (+ (+ (* 3 a) b) c) -3)
        (equal (+ (+ a (* 3 b)) c) 9)
        (equal (+ (+ a b) (* 3 c)) 19))
   (equal (* (* a b) c) -56)))

(value-triple :itpeval-statement-checked)
:q
