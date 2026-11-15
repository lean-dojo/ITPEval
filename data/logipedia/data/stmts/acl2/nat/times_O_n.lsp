;; Statement-only formalization of Logipedia corpus artifact nat.times_O_n,
;; catalog title "nat.times_O_n": for every natural number n, multiplying
;; zero by n yields zero. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-times-o-n-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal
      0
      (* 0 n)))))

(value-triple :itpeval-statement-checked)
:q
