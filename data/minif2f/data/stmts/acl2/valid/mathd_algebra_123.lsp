;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_123:
;; positive natural numbers a and b satisfying a + b = 20 and a = 3*b have
;; natural-number difference a - b = 10. This file contains no proof.

(in-package "ACL2")

;; Under a = 3*b with positive b, ACL2 integer subtraction agrees with the
;; truncated natural subtraction used by the natural-number source statements.
(defun mathd-algebra-123-statement (a b)
  (implies
   (and (natp a)
        (natp b)
        (< 0 a)
        (< 0 b)
        (equal (+ a b) 20)
        (equal a (* 3 b)))
   (equal (- a b) 10)))

(value-triple :itpeval-statement-checked)
:q
