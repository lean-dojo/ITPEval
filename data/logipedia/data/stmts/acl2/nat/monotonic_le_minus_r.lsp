;; Statement-only formalization of Logipedia corpus artifact
;; nat.monotonic_le_minus_r, catalog title "nat.monotonic_le_minus_r": for
;; natural numbers p, q, and n, q <= p implies n - p <= n - q, where
;; subtraction is truncated at zero. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-monotonic-le-minus-r-minus (x y)
  (nfix (- x y)))

(defun-sk logipedia-nat-monotonic-le-minus-r-statement ()
  (forall (p q n)
    (implies
     (and
      (natp p)
      (natp q)
      (natp n)
      (<= q p))
     (<=
      (logipedia-nat-monotonic-le-minus-r-minus n p)
      (logipedia-nat-monotonic-le-minus-r-minus n q)))))

(value-triple :itpeval-statement-checked)
:q
