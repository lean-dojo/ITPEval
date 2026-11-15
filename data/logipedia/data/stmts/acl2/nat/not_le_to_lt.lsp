;; Statement-only formalization of Logipedia corpus artifact
;; nat.not_le_to_lt, catalog title "nat.not_le_to_lt": for all natural
;; numbers n and m, if n is not less than or equal to m, then m is less
;; than n. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-not-le-to-lt-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (implies
      (not (<= n m))
      (< m n)))))

(value-triple :itpeval-statement-checked)
:q
