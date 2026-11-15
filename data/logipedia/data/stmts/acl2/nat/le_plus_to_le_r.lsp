;; Statement-only formalization of Logipedia corpus artifact
;; nat.le_plus_to_le_r, catalog title "nat.le_plus_to_le_r": for natural
;; numbers, right-addition by the same value reflects less-than-or-equal.
;; This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-le-plus-to-le-r-statement (a n m)
  (implies
   (and (natp a)
        (natp n)
        (natp m)
        (<= (+ n a)
            (+ m a)))
   (<= n m)))

(value-triple :itpeval-statement-checked)
:q
