;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_144:
;; positive natural numbers a, b, c, and d with equal successive differences,
;; a + b + c = 60, and a + b > c satisfy d < 10. This file contains no proof.

(in-package "ACL2")

;; Since d is positive, the two difference equalities force c > b > a.
;; ACL2 integer subtraction therefore agrees with the truncated natural
;; subtraction used by the natural-number source statements.
(defun mathd-algebra-144-statement (a b c d)
  (implies
   (and (natp a)
        (natp b)
        (natp c)
        (natp d)
        (< 0 a)
        (< 0 b)
        (< 0 c)
        (< 0 d)
        (equal (- c b) d)
        (equal (- b a) d)
        (equal (+ a b c) 60)
        (< c (+ a b)))
   (< d 10)))

(value-triple :itpeval-statement-checked)
:q
