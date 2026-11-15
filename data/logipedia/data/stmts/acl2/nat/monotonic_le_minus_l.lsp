;; Statement-only formalization of Logipedia corpus artifact
;; nat.monotonic_le_minus_l, catalog title "nat.monotonic_le_minus_l":
;; for natural numbers p, q, and n, q <= p implies that truncated subtraction
;; of n preserves this order. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-monotonic-le-minus-l-minus (x y)
  (nfix (- x y)))

(defun-sk logipedia-nat-monotonic-le-minus-l-statement ()
  (forall (p q n)
    (implies
     (and
      (natp p)
      (natp q)
      (natp n)
      (<= q p))
     (<=
      (logipedia-nat-monotonic-le-minus-l-minus q n)
      (logipedia-nat-monotonic-le-minus-l-minus p n)))))

(value-triple :itpeval-statement-checked)
:q
