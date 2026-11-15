;; Statement-only formalization of Logipedia corpus artifact
;; nat.monotonic_le_times_r, catalog title "nat.monotonic_le_times_r":
;; multiplication by a fixed natural number on the left is monotone with
;; respect to natural-number order. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-monotonic-le-times-r-statement ()
  (forall (n x y)
    (implies
     (and
      (natp n)
      (natp x)
      (natp y)
      (<= x y))
     (<= (* n x) (* n y)))))

(value-triple :itpeval-statement-checked)
:q
