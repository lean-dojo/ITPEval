;; Statement-only formalization of Logipedia corpus artifact
;; nat.not_le_to_not_le_S_S, catalog title "nat.not_le_to_not_le_S_S": for
;; all natural numbers n and m, if n is not at most m, then successor n is
;; not at most successor m. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-not-le-to-not-le-s-s-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (implies
      (not (<= n m))
      (not (<= (1+ n) (1+ m)))))))

(value-triple :itpeval-statement-checked)
:q
