;; Statement-only formalization of Logipedia corpus artifact
;; nat.distributive_times_plus_r, catalog title
;; "nat.distributive_times_plus_r": right multiplication on natural numbers
;; distributes over addition. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-distributive-times-plus-r-statement ()
  (forall (a b c)
    (implies
     (and (natp a)
          (natp b)
          (natp c))
     (equal
      (* (+ b c) a)
      (+ (* b a) (* c a))))))

(value-triple :itpeval-statement-checked)
:q
