;; Statement-only formalization of Logipedia corpus artifact
;; nat.not_le_S_S_to_not_le, catalog title "nat.not_le_S_S_to_not_le": for
;; all natural numbers n and m, if successor n is not at most successor m,
;; then n is not at most m. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-not-le-s-s-to-not-le-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (implies
      (not (<= (1+ n) (1+ m)))
      (not (<= n m))))))

(value-triple :itpeval-statement-checked)
:q
