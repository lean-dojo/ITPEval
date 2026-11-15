;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_35:
;; the real functions p(x) = 2 - x^2 and q(x) = 6/x for nonzero x satisfy
;; p(q(2)) = -7. This file contains no proof.
;;
;; The source hypotheses determine q(2) and then p(q(2)) uniquely, so replacing
;; those values by the definitions below yields exactly the displayed closed
;; evaluation. Conversely, these definitions give real functions satisfying
;; the source hypotheses (with q(0) arbitrary), and any source functions
;; satisfying the hypotheses agree with them at every value used here. Thus
;; eliminating the universally quantified functions is bidirectionally
;; equivalent. All remaining values are rational constants represented exactly
;; by ACL2, so this introduces no restriction on a free real variable.

(in-package "ACL2")

(defun mathd-algebra-35-p (x)
  (- 2 (* x x)))

(defun mathd-algebra-35-q (x)
  (/ 6 x))

(defun mathd-algebra-35-statement ()
  (equal (mathd-algebra-35-p
          (mathd-algebra-35-q 2))
         -7))

(value-triple :itpeval-statement-checked)
:q
