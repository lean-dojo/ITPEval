;; Statement-only formalization of Logipedia corpus artifact nat.plus_n_Sm,
;; catalog title "nat.plus_n_Sm": for all natural numbers n and m,
;; S(n + m) = n + S(m). This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-plus-n-sm-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (equal
      (+ (+ n m) 1)
      (+ n (+ m 1))))))

(value-triple :itpeval-statement-checked)
:q
