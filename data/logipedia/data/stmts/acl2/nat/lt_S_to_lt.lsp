;; Statement-only formalization of Logipedia corpus artifact nat.lt_S_to_lt,
;; catalog title "nat.lt_S_to_lt": if the successor of one natural number is
;; strictly less than another, then the original number is strictly less than
;; it. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-lt-s-to-lt-statement (n m)
  (implies
   (and (natp n)
        (natp m)
        (< (1+ n) m))
   (< n m)))

(value-triple :itpeval-statement-checked)
:q
