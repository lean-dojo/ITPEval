;; Statement-only formalization of Logipedia corpus artifact
;; nat.distributive_times_plus, catalog title
;; "nat.distributive_times_plus": left multiplication on natural numbers
;; distributes over addition. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-distributive-times-plus-statement ()
  (forall (a b c)
    (implies
     (and (natp a)
          (natp b)
          (natp c))
     (equal
      (* a (+ b c))
      (+ (* a b) (* a c))))))

(value-triple :itpeval-statement-checked)
:q
