;; Statement-only formalization of Logipedia corpus artifact
;; nat.lt_to_le_to_lt, catalog title "nat.lt_to_le_to_lt": for natural
;; numbers n, m, and p, n < m and m <= p imply n < p. This file contains no
;; proof.

(in-package "ACL2")

(defun logipedia-nat-lt-to-le-to-lt-statement (n m p)
  (implies
   (and (natp n)
        (natp m)
        (natp p))
   (implies
    (< n m)
    (implies
     (<= m p)
     (< n p)))))

(value-triple :itpeval-statement-checked)
:q
