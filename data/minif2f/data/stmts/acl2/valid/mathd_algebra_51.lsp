;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_51:
;; for positive real numbers a and b, if a + b = 35 and a = (2/5) * b,
;; then b - a = 15. This file contains no proof.
;;
;; ACL2 exact rational arithmetic is bidirectionally equivalent here. The two
;; source equations force b = 25 and a = 10, so every satisfying real pair is
;; rational. Conversely, every guarded ACL2 pair embeds unchanged into the
;; reals with the same assumptions and conclusion.

(in-package "ACL2")

(defun mathd-algebra-51-statement (a b)
  (implies
   (and (rationalp a)
        (rationalp b)
        (< 0 a)
        (< 0 b)
        (equal (+ a b) 35)
        (equal a (* (/ 2 5) b)))
   (equal (- b a) 15)))

(value-triple :itpeval-statement-checked)
:q
