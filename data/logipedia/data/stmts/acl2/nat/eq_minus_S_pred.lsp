;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_minus_S_pred, catalog title "nat.eq_minus_S_pred": for all natural
;; numbers n and m, subtracting the successor of m from n equals the
;; predecessor of the truncated natural difference n - m. This file contains
;; no proof.

(in-package "ACL2")

(defun logipedia-nat-eq-minus-s-pred-predecessor (n)
  (if (zp n)
      0
    (- n 1)))

(defun-sk logipedia-nat-eq-minus-s-pred-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (equal
      (nfix (- n (+ m 1)))
      (logipedia-nat-eq-minus-s-pred-predecessor
       (nfix (- n m)))))))

(value-triple :itpeval-statement-checked)
:q
