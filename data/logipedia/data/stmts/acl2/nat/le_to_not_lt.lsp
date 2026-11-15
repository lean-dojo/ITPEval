;; Statement-only formalization of Logipedia corpus artifact
;; nat.le_to_not_lt, catalog title "nat.le_to_not_lt": for all natural
;; numbers n and m, n <= m implies that m is not less than n. This file
;; contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-le-to-not-lt-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (implies
      (<= n m)
      (not (< m n))))))

(value-triple :itpeval-statement-checked)
:q
