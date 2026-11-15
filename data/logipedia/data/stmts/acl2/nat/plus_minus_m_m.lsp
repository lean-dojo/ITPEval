;; Statement-only formalization of Logipedia corpus artifact
;; nat.plus_minus_m_m, catalog title "nat.plus_minus_m_m": for natural
;; numbers n and m with m <= n, n equals its truncated difference n - m
;; plus m. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-plus-minus-m-m-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (implies
      (<= m n)
      (equal n
             (+ (nfix (- n m)) m))))))

(value-triple :itpeval-statement-checked)
:q
