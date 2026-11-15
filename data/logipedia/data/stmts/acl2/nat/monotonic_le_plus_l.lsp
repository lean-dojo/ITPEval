;; Statement-only formalization of Logipedia corpus artifact
;; nat.monotonic_le_plus_l, catalog title "nat.monotonic_le_plus_l":
;; adding a fixed natural number on the right is monotone with respect to
;; natural-number order. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-monotonic-le-plus-l-statement ()
  (forall (m x y)
    (implies
     (and
      (natp m)
      (natp x)
      (natp y)
      (<= x y))
     (<= (+ x m) (+ y m)))))

(value-triple :itpeval-statement-checked)
:q
