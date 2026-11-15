;; Statement-only formalization of Logipedia corpus artifact nat.times_Sn_m,
;; catalog title "nat.times_Sn_m": for all natural numbers n and m, m plus
;; n times m equals the product of the successor of n with m. This file
;; contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-times-sn-m-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (equal
      (+ m (* n m))
      (* (+ n 1) m)))))

(value-triple :itpeval-statement-checked)
:q
