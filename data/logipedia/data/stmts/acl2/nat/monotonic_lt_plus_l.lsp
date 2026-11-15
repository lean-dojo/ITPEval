;; Statement-only formalization of Logipedia corpus artifact
;; nat.monotonic_lt_plus_l, catalog title "nat.monotonic_lt_plus_l":
;; adding a fixed natural number on the right is strictly monotone with
;; respect to natural-number order. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-monotonic-lt-plus-l-statement ()
  (forall (n x y)
    (implies
     (and
      (natp n)
      (natp x)
      (natp y)
      (< x y))
     (< (+ x n) (+ y n)))))

(value-triple :itpeval-statement-checked)
:q
