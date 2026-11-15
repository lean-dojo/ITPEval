;; Statement-only formalization of miniF2F artifact mathd_algebra_209: a
;; bijection of the reals whose inverse sends 2 to 10, 10 to 1, and 1 to 2
;; satisfies sigma(sigma(10)) = 1. This file contains no proof.
;;
;; ACL2 is first-order, so the bijection is represented by the observations
;; used in the source argument. Equal inputs have equal sigma-values, and
;; sigma(sigma-inverse(x)) = x is recorded at x = 2 and x = 1. Every source
;; bijection induces these equalities. Conversely, the antecedent forces the
;; same local orbit as the real bijection cycling 1 to 10, 10 to 2, and 2 to
;; 1, extended by the identity elsewhere. Thus the observation encoding is
;; bidirectionally equivalent to the source statement.

(in-package "ACL2")

(defun mathd-algebra-209-statement
    (inverse-at-two
     inverse-at-ten
     inverse-at-one
     sigma-at-inverse-at-two
     sigma-at-ten
     sigma-at-inverse-at-one
     sigma-at-two
     sigma-at-sigma-at-ten)
  (implies
   (and
    (equal inverse-at-two 10)
    (equal inverse-at-ten 1)
    (equal inverse-at-one 2)
    (equal sigma-at-inverse-at-two sigma-at-ten)
    (equal sigma-at-inverse-at-two 2)
    (equal sigma-at-inverse-at-one sigma-at-two)
    (equal sigma-at-inverse-at-one 1)
    (equal sigma-at-sigma-at-ten sigma-at-two))
   (equal sigma-at-sigma-at-ten 1)))

(value-triple :itpeval-statement-checked)
:q
