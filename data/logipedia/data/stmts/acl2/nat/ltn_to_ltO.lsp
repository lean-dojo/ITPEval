;; Statement-only formalization of Logipedia corpus artifact nat.ltn_to_ltO,
;; catalog title "nat.ltn_to_ltO": for all natural numbers n and m, n < m
;; implies 0 < m. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-ltn-to-lto-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (implies
      (< n m)
      (< 0 m)))))

(value-triple :itpeval-statement-checked)
:q
