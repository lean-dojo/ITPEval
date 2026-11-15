;; Statement-only formalization of Logipedia corpus artifact
;; primes.divides_n_O, catalog title "primes.divides_n_O": every natural
;; number divides zero, with divisibility witnessed by a natural quotient.
;; This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-primes-divides-n-o-divides-p (n m)
  (exists (q)
    (and
     (natp q)
     (equal m (* n q)))))

(defun-sk logipedia-primes-divides-n-o-statement ()
  (forall (n)
    (implies
     (natp n)
     (logipedia-primes-divides-n-o-divides-p n 0))))

(value-triple :itpeval-statement-checked)
:q
