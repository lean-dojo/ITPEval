;; Statement-only formalization of Logipedia corpus artifact
;; nat.le_plus_to_minus, catalog title "nat.le_plus_to_minus": for natural
;; numbers, n <= p + m implies that the truncated difference n - m is at
;; most p. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-le-plus-to-minus-statement ()
  (forall (n m p)
    (implies
     (and (natp n)
          (natp m)
          (natp p))
     (implies
      (<= n (+ p m))
      (<= (nfix (- n m)) p)))))

(value-triple :itpeval-statement-checked)
:q
