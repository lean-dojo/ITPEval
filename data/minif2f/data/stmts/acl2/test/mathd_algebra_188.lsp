;; Statement-only formalization of miniF2F artifact mathd_algebra_188: a
;; bijection of the reals whose value and inverse value at 2 agree maps that
;; common value back to 2. The Rocq and Metamath sources specialize the common
;; value to 4. This file contains no proof.
;;
;; ACL2 is first-order, so the bijection is represented by its four relevant
;; observations. The second equality is function congruence for the equal
;; inputs in the first equality, and the third is the inverse law at 2.
;; Conversely, every satisfying equality pattern is realized over the reals:
;; use the identity when the common value is 2, and otherwise transpose 2 with
;; that value, extending arbitrarily by the identity. Since only equality and
;; the distinguished value 2 occur, arbitrary ACL2 values preserve exactly
;; the real equality patterns used by the source statement.

(in-package "ACL2")

(defun mathd-algebra-188-statement
    (sigma-at-two
     inverse-at-two
     sigma-at-sigma-at-two
     sigma-at-inverse-at-two)
  (implies
   (and
    (equal sigma-at-two inverse-at-two)
    (equal sigma-at-sigma-at-two
           sigma-at-inverse-at-two)
    (equal sigma-at-inverse-at-two 2))
   (equal sigma-at-sigma-at-two 2)))

(value-triple :itpeval-statement-checked)
:q
