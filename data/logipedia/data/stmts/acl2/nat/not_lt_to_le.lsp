;; Statement-only formalization of Logipedia corpus artifact
;; nat.not_lt_to_le, catalog title "nat.not_lt_to_le": for all natural
;; numbers n and m, if n is not less than m, then m is less than or equal
;; to n. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-not-lt-to-le-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (implies
      (not (< n m))
      (<= m n)))))

(value-triple :itpeval-statement-checked)
:q
