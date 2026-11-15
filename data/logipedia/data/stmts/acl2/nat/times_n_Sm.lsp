;; Statement-only formalization of Logipedia corpus artifact nat.times_n_Sm,
;; catalog title "nat.times_n_Sm": for all natural numbers n and m,
;; n + n*m = n*S(m). This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-times-n-sm-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (equal
      (+ n (* n m))
      (* n (+ m 1))))))

(value-triple :itpeval-statement-checked)
:q
