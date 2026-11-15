;; Statement-only formalization of Logipedia corpus artifact
;; nat.monotonic_lt_times_r, catalog title "nat.monotonic_lt_times_r": for
;; every positive natural multiplier, left multiplication is strictly
;; monotone on natural numbers. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-monotonic-lt-times-r-statement ()
  (forall (c x y)
    (implies
     (and (natp c)
          (natp x)
          (natp y))
     (implies
      (< 0 c)
      (implies
       (< x y)
       (< (* c x) (* c y)))))))

(value-triple :itpeval-statement-checked)
:q
