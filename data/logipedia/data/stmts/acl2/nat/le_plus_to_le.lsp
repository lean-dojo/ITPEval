;; Statement-only formalization of Logipedia corpus artifact nat.le_plus_to_le,
;; catalog title "nat.le_plus_to_le": cancellation of a common left addend
;; preserves less-than-or-equal on natural numbers. This file contains no
;; proof.

(in-package "ACL2")

(defun logipedia-nat-le-plus-to-le-statement (a n m)
  (implies
   (and (natp a)
        (natp n)
        (natp m)
        (<= (+ a n)
            (+ a m)))
   (<= n m)))

(value-triple :itpeval-statement-checked)
:q
