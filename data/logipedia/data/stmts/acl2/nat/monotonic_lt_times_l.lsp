;; Statement-only formalization of Logipedia corpus artifact
;; nat.monotonic_lt_times_l, catalog title "nat.monotonic_lt_times_l":
;; multiplication by a fixed positive natural number on the right is strictly
;; monotone with respect to natural-number order. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-monotonic-lt-times-l-statement ()
  (forall (c x y)
    (implies
     (and
      (natp c)
      (natp x)
      (natp y)
      (< 0 c)
      (< x y))
     (< (* x c) (* y c)))))

(value-triple :itpeval-statement-checked)
:q
